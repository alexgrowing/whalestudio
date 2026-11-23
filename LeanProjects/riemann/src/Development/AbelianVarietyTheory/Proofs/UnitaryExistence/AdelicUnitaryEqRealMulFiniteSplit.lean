import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.UnitarySplit

section Gen

open Formalism.UG

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem val_bc (p : R →+* A) (g : GL n R) : ((bc p g : GL n A) : Matrix n n A) = (g : Matrix n n R).map p := rfl

theorem mat_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {M N : Matrix n n R}
    (h1 : M.map p = N.map p) (h2 : M.map q = N.map q) : M = N := by
  ext i j
  exact hi _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem gl_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {g h : GL n R}
    (h1 : bc p g = bc p h) (h2 : bc q g = bc q h) : g = h :=
  Units.ext (mat_ext p q hi (congrArg Units.val h1) (congrArg Units.val h2))

theorem gl_glue (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (hs : ∀ a b, ∃ x, p x = a ∧ q x = b) (a : GL n A) (b : GL n B) : ∃ g : GL n R, bc p g = a ∧ bc q g = b := by
  choose f hp hq using hs
  let G : Matrix n n A → Matrix n n B → Matrix n n R := fun M N => Matrix.of fun i j => f (M i j) (N i j)
  have Gp : ∀ M N, (G M N).map p = M := fun M N => by ext i j; simp [G, hp]
  have Gq : ∀ M N, (G M N).map q = N := fun M N => by ext i j; simp [G, hq]
  refine ⟨⟨G a.1 b.1, G (a⁻¹).1 (b⁻¹).1, ?_, ?_⟩, Units.ext (Gp _ _), Units.ext (Gq _ _)⟩ <;>
    apply mat_ext p q hi <;> simp [Matrix.map_mul, Gp, Gq]

theorem map_cond (p : R →+* A) (s : R →+* R) (t : A →+* A) (hc : ∀ x, p (s x) = t (p x)) (J g : Matrix n n R) :
    (cT s g * J * g).map p = cT t (g.map p) * J.map p * g.map p := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hc]

theorem mem_iff (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (s : R →+* R) (t : A →+* A) (u : B →+* B) (hp : ∀ x, p (s x) = t (p x)) (hq : ∀ x, q (s x) = u (q x))
    (J : Matrix n n R) (g : GL n R) :
    g ∈ UJ s J ↔ bc p g ∈ UJ t (J.map p) ∧ bc q g ∈ UJ u (J.map q) := by
  change cT s g.1 * J * g.1 = J ↔ cT t (g.1.map p) * J.map p * g.1.map p = J.map p ∧
    cT u (g.1.map q) * J.map q * g.1.map q = J.map q
  rw [← map_cond p s t hp, ← map_cond q s u hq]
  exact ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun h => mat_ext p q hi h.1 h.2⟩

theorem mem_of_form (t : A →+* A) (J : Matrix n n A) (g : GL n A)
    (h : ∀ x y, hform t J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform t J x y) : g ∈ UJ t J := by
  change cT t g.1 * J * g.1 = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [hform, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] at this
  rw [Finset.sum_comm] at this
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [this, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end Gen

section Tens

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem map_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_JR (f : R →ₐ[F] R') {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (JR R J).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = JR R' J := by
  ext i j
  simp [JR, inclR]

end Tens

variable {D : D7}

theorem parts_inj (D : D7) (x y : AE D) (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem parts_surj (D : D7) (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : AE D, infPart D x = a ∧ finPart D x = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem mem_parts (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram ↔
      Formalism.UG.bc (infPart D) g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram ∧
        Formalism.UG.bc (finPart D) g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have := mem_iff (infPart D) (finPart D) (parts_inj D) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig)
    (sigR _ D.sp.cm.sig) (map_sig _ _) (map_sig _ _) (JR _ V.gram) g
  rw [show (JR _ V.gram).map (infPart D) = JR _ V.gram from map_JR _ _,
    show (JR _ V.gram).map (finPart D) = JR _ V.gram from map_JR _ _] at this
  exact this

theorem ga_ext (V : HSp D) {g h : GA D V} (h1 : infHom V g = infHom V h) (h2 : finHom V g = finHom V h) : g = h :=
  Subtype.ext (gl_ext (infPart D) (finPart D) (parts_inj D) h1 h2)

theorem ga_glue (V : HSp D) (a : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (b : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (ha : a ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram)
    (hb : b ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) : ∃ g : GA D V, infHom V g = a ∧ finHom V g = b := by
  obtain ⟨g, h1, h2⟩ := gl_glue (infPart D) (finPart D) (parts_inj D) (parts_surj D) a b
  exact ⟨⟨g, (mem_parts V g).2 ⟨h1 ▸ ha, h2 ▸ hb⟩⟩, h1, h2⟩

theorem infHom_mem (V : HSp D) (g : GA D V) : infHom V g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).1

theorem finHom_mem (V : HSp D) (g : GA D V) : finHom V g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).2

theorem hermA_eq (V : HSp D) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y =
      Formalism.UG.hform (sigR (Af D.host.F) D.sp.cm.sig) (JR (Af D.host.F) V.gram) y x := by
  unfold GlobalTheory.AdLat.hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * (JR (Af D.host.F) V.gram a b) * sigR (Af D.host.F) D.sp.cm.sig (y a) = _
  ring

theorem real_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ?_, fun h h1 h2 => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V _ 1 (infHom_mem V h) (one_mem _)
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 _ (one_mem _) (finHom_mem V h)
    refine ⟨a, a2, k, k1, ga_ext V ?_ ?_⟩
    · rw [map_mul, a1, k1, mul_one]
    · rw [map_mul, a2, k2, one_mul]
  · have a2 : finHom V a = 1 := ha
    have k1 : infHom V k = 1 := hk
    refine ga_ext V ?_ ?_
    · rw [map_mul, map_mul, k1, mul_one, one_mul]
    · rw [map_mul, map_mul, a2, mul_one, one_mul]
  · have a2 : finHom V h = 1 := h1
    have k1 : infHom V h = 1 := h2
    exact ga_ext V (by rw [k1, map_one]) (by rw [a2, map_one])
  · have hm : g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
      mem_of_form _ _ g fun x y => by rw [← hermA_eq, ← hermA_eq, hg]
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 g (one_mem _) hm
    exact ⟨k, k1, k2⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V g 1 hg (one_mem _)
    exact ⟨a, a2, a1⟩

end GlobalTheory.UnitarySplit
