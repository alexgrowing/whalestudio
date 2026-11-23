import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct Matrix

namespace GlobalTheory.TwV.LbB

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

def FrAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F

def IntB (A : LocAt F E n G) (v : Fin G.P.nV) (t : Fin n → G.P.Qq v) : Prop :=
  ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
    Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ (fun k => A.eQ v (t k))) a ∈ (A.pl v).1.adicCompletionIntegers F

theorem intB_zero (A : LocAt F E n G) (v : Fin G.P.nV) : IntB A v 0 := by
  intro a
  have : (fun k => A.eQ v ((0 : Fin n → G.P.Qq v) k)) = 0 := by funext k; simp
  rw [this, Matrix.mulVec_zero]
  exact zero_mem _

theorem intB_add (A : LocAt F E n G) (v : Fin G.P.nV) (t t' : Fin n → G.P.Qq v) (h : IntB A v t) (h' : IntB A v t') :
    IntB A v (t + t') := by
  intro a
  have : (fun k => A.eQ v ((t + t') k)) = (fun k => A.eQ v (t k)) + (fun k => A.eQ v (t' k)) := by funext k; simp
  rw [this, Matrix.mulVec_add]
  exact add_mem (h a) (h' a)

theorem intB_smul (A : LocAt F E n G) (hW : LocInt A) (v : Fin G.P.nV) (c : G.P.W v) (t : Fin n → G.P.Qq v) (h : IntB A v t) :
    IntB A v (c • t) := by
  intro a
  have : (fun k => A.eQ v ((c • t) k)) = A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) c) • (fun k => A.eQ v (t k)) := by
    funext k
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl
  rw [this, Matrix.mulVec_smul]
  exact mul_mem ((hW v _).1 ⟨c, rfl⟩) (h a)

theorem mulVec_inv_mulVec {R : Type} [CommRing R] (y : GL (Fin n) R) (u : Fin n → R) :
    (y : Matrix (Fin n) (Fin n) R) *ᵥ (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mem_colSpan {Qq W : Type} [CommRing W] [Field Qq] [Algebra W Qq] (M : Matrix (Fin n) (Fin n) Qq) (r : Fin n → W) :
    M *ᵥ (fun c => algebraMap W Qq (r c)) ∈ colSpan W M := by
  have : M *ᵥ (fun c => algebraMap W Qq (r c)) = ∑ c, r c • (fun i => M i c) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem fst_mem_span (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (v : Fin G.P.nV)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F)
    (hx : x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb) :
    (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) ∈
      Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
  unfold Formalism.L2.Herm.locL latS at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((0 : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F) a)).1)) = 0 := by
      funext a; simp
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((x + y) a)).1)) =
        (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) + (fun a => (A.eQ v).symm ((A.spl v (y a)).1)) := by
      funext a; simp
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    have hs := (split_integral_completion F E (A.pl v).1 (A.spl v) (hAlg v) s).1 s.2
    obtain ⟨c, hc⟩ := (hW v ((A.eQ v).symm ((A.spl v s).1))).2 (by rw [RingEquiv.apply_symm_apply]; exact hs.1)
    have : (fun a => (A.eQ v).symm ((A.spl v ((s • x) a)).1)) = c • (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) := by
      funext a
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, map_mul, Pi.smul_apply, Algebra.smul_def, hc]
    rw [this]
    exact Submodule.smul_mem _ c hx

set_option maxHeartbeats 400000 in

theorem lbAt_gen (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) (v : Fin G.P.nV) :
    Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) =
      colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) := by
  set fr : GL (Fin n) ((A.pl v).1.adicCompletion F) := bc (A.phE v) A.B with hfrdef
  have hM : ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) =
      (fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) := by
    ext a b; rfl

  have h1 : ∀ t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))), IntB A v t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have hloc : (fun k => inclE (F := F) ((A.pl v).1.adicCompletion F) (y k)) ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have := (hfr v (fun k => A.eQ v (A.iw v (y k)))).1 ⟨_, hloc, fun a => by
        show (A.ph v) (inclE (F := F) ((A.pl v).1.adicCompletion F) (y a)) = A.eQ v ((A.eQ v).symm (A.phE v (y a)))
        rw [RingEquiv.apply_symm_apply]
        rfl⟩
      exact this
    | zero => exact intB_zero A v
    | add x y _ _ hx hy => exact intB_add A v x y hx hy
    | smul c x _ hx => exact intB_smul A hW v c x hx

  have h2 : ∀ t, IntB A v t → ∃ r : Fin n → G.P.W v,
      t = ((fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)) *ᵥ
        (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) := by
    intro t ht
    choose r hr using fun c => (hW v ((A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => A.eQ v (t k))) c))).2 (by rw [RingEquiv.apply_symm_apply]; exact ht c)
    refine ⟨r, ?_⟩
    have e1 : (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) =
        fun c => (A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) c) := by
      funext c; exact hr c
    rw [e1]
    funext i
    have e2 := RingHom.map_mulVec ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (fr : Matrix (Fin n) (Fin n) _)
      (((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) i
    rw [mulVec_inv_mulVec] at e2
    exact (RingEquiv.symm_apply_apply (A.eQ v) (t i)).symm.trans e2

  have h3 : ∀ t, IntB A v t →
      t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
    intro t ht
    obtain ⟨x, hx, hxa⟩ := (hfr v (fun k => A.eQ v (t k))).2 ht
    have h4 := fst_mem_span A hW hAlg v Lb x hx
    have e3 : (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) = t := by
      funext a; rw [hxa a]; exact RingEquiv.symm_apply_apply _ _
    rw [e3] at h4
    exact h4
  apply le_antisymm
  · intro t ht
    obtain ⟨r, rfl⟩ := h2 t (h1 t ht)
    rw [hM]
    exact mulVec_mem_colSpan _ r
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    apply h3
    intro a
    have hcol : (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c)) =
        fun k => (fr : Matrix (Fin n) (Fin n) _) k c := by
      funext k; rw [hM, Matrix.map_apply]; exact RingEquiv.apply_symm_apply _ _
    show ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
      (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c))) a ∈ _
    rw [hcol]
    have e4 : (((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ
        fun k => (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) k c) a =
        ((((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *
          (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) a c) := by
      simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [e4, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem frAtB_re [StarRing E] {r N : ℕ} (h : r = N) (A : LocAt F E N G) (Lb : Submodule (𝓞 E) (Fin r → E)) (B0 : GL (Fin r) E)
    (hB : A.B = Formalism.L2.Forms.reGL h E B0) (fr : ∀ v, GL (Fin r) ((A.pl v).1.adicCompletion F))
    (hfr0 : ∀ v (t : Fin r → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
        ∀ a, ((((fr v)⁻¹ : GL (Fin r) ((A.pl v).1.adicCompletion F)) :
          Matrix (Fin r) (Fin r) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hrat : ∀ v, fr v = bc (A.phE v) B0) :
    FrAtB A (Lb.map (((reE (E := E) h : (Fin r → E) ≃ₗ[E] (Fin N → E)) : (Fin r → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))) := by
  subst h
  rw [Formalism.MainNotions.G.KAat.map_reE_rfl]
  have hre : Formalism.L2.Forms.reGL (rfl : r = r) E B0 = B0 := by apply Units.ext; ext a b; rfl
  rw [hre] at hB
  intro v t
  rw [hB, ← hrat v]
  exact hfr0 v t

end Gen

section Of

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

theorem lbAtB_of (A : LocAt F E n G) (hW : LocInt A) (hAlg : SplAlg A)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) : GlobalTheory.TwV.LbAtB A Lb := by
  intro v
  unfold GlobalTheory.TwV.locSp
  exact lbAt_gen A hW hAlg Lb hfr v

end Of

end GlobalTheory.TwV.LbB

end
