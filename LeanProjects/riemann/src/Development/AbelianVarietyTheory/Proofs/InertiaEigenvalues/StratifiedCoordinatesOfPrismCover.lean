import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushoutStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SiteCoord

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem comp_assoc {R : Type} [CommRing R] {P₁ P₂ P₃ P₄ : Obj l R} (a : Hom P₃ P₄) (b : Hom P₂ P₃)
    (c : Hom P₁ P₂) : (a.comp b).comp c = a.comp (b.comp c) := Hom.ext' rfl

theorem map_mulVec (S : Strat bk d) {Y Y' : Obj l ↥(OL K)} (k : Hom Y Y') (g₁ g₂ : Hom bk.prism Y)
    (w : Fin d → Y.A) :
    (fun i => k.f ((S.ε g₁ g₂).mulVec w i)) = (S.ε (k.comp g₁) (k.comp g₂)).mulVec fun i => k.f (w i) := by
  funext i
  rw [RingHom.map_mulVec, S.ε_nat]
  rfl

theorem mulVec_map_add {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (w w' : Fin d → A) :
    M.mulVec (fun i => φ ((w + w') i)) = M.mulVec (fun i => φ (w i)) + M.mulVec (fun i => φ (w' i)) := by
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem mulVec_map_smul {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (c : A) (w : Fin d → A) : M.mulVec (fun i => φ ((c • w) i)) = φ c • M.mulVec (fun i => φ (w i)) := by
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem coords_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  intro l _ K bk d S B C h f hC P _ _ u hu Q a g
  obtain ⟨Q₀, a₀, h₀, hpo⟩ := hC.stable.po Q a
  have hc₀ : Cover h₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hC
  obtain ⟨hinj, hsh⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀
  obtain ⟨D, p, q, hpq⟩ := hc₀.stable.po Q₀ h₀
  have hcf : ∀ b, a₀.f (h.f b) = h₀.f (a.f b) := fun b => congrArg (fun k : Hom B Q₀ => k.f b) hpo.comm
  obtain ⟨z, hzdef⟩ : ∃ z : P → Fin d → Q₀.A,
      z = fun x => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := ⟨_, rfl⟩
  have hpa : (p.comp a₀).comp h = (q.comp a₀).comp h := by
    rw [comp_assoc p a₀ h, comp_assoc q a₀ h, hpo.comm, ← comp_assoc p h₀ a, ← comp_assoc q h₀ a, hpq.comm]
  have hg : p.comp (h₀.comp g) = q.comp (h₀.comp g) := by rw [← comp_assoc p h₀ g, hpq.comm, comp_assoc q h₀ g]
  have key : ∀ x, (fun i => p.f (z x i)) = fun i => q.f (z x i) := by
    intro x
    have e1 := hu D (p.comp a₀) (q.comp a₀) hpa x
    simp only [comp_assoc] at e1
    have e1' : (fun i => p.f (a₀.f (u x i))) = (S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
        fun i => q.f (a₀.f (u x i)) := e1
    have e2 := map_mulVec S p (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have e3 := map_mulVec S q (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have hzx : z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := by rw [hzdef]
    calc (fun i => p.f (z x i))
        = fun i => p.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
          congrArg (fun w : Fin d → Q₀.A => fun i => p.f (w i)) hzx
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec fun i => p.f (a₀.f (u x i)) := e2
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec
            ((S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i))) :=
          congrArg (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec e1'
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f)) * S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
            fun i => q.f (a₀.f (u x i)) := Matrix.mulVec_mulVec _ _ _
      _ = (S.ε (p.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun M => Matrix.mulVec M fun i => q.f (a₀.f (u x i))) (S.ε_trans _ _ _)
      _ = (S.ε (q.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun k => Matrix.mulVec (S.ε k (q.comp (a₀.comp f))) fun i => q.f (a₀.f (u x i))) hg
      _ = fun i => q.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) := e3.symm
      _ = fun i => q.f (z x i) := (congrArg (fun w : Fin d → Q₀.A => fun i => q.f (w i)) hzx).symm
  have hz : ∀ x i, ∃ y, h₀.f y = z x i := fun x i => by
    obtain ⟨y, hy⟩ := hsh D p q hpq (z x i) (congrFun (key x) i)
    exact ⟨y, hy⟩
  choose y hy using hz
  have hzx : ∀ x, z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := fun x => congrFun hzdef x
  have z_add : ∀ x x', z (x + x') = z x + z x' := fun x x' =>
    calc z (x + x') = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (x + x') i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((u x + u x') i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i)) (map_add u x x')
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) +
            (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x' i)) := mulVec_map_add a₀.f _ _ _
      _ = z x + z x' := congrArg₂ (· + ·) (hzx x).symm (hzx x').symm
  have z_smul : ∀ (b : B.A) x, z (b • x) = h₀.f (a.f b) • z x := fun b x =>
    calc z (b • x) = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (b • x) i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((h.f b • u x) i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i))
            (LinearMap.map_smulₛₗ u b x)
      _ = a₀.f (h.f b) • (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) := mulVec_map_smul a₀.f _ _ _
      _ = h₀.f (a.f b) • z x := congrArg₂ (· • ·) (hcf b) (hzx x).symm
  let v : P →ₛₗ[a.f] (Fin d → Q.A) :=
    { toFun := y
      map_add' := fun x x' => by
        funext i
        apply hinj
        exact calc h₀.f (y (x + x') i) = z (x + x') i := hy _ i
          _ = z x i + z x' i := congrFun (z_add x x') i
          _ = h₀.f (y x i) + h₀.f (y x' i) := congrArg₂ (· + ·) (hy x i).symm (hy x' i).symm
          _ = h₀.f (y x i + y x' i) := (map_add h₀.f _ _).symm
      map_smul' := fun b x => by
        funext i
        apply hinj
        exact calc h₀.f (y (b • x) i) = z (b • x) i := hy _ i
          _ = h₀.f (a.f b) * z x i := congrFun (z_smul b x) i
          _ = h₀.f (a.f b) * h₀.f (y x i) := congrArg (h₀.f (a.f b) * ·) (hy x i).symm
          _ = h₀.f (a.f b * y x i) := (map_mul h₀.f _ _).symm }
  refine ⟨v, ?_⟩
  intro Q' h' a' hcomm x
  have hU := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C Q Q₀ h a a₀ h₀ hpo Q' a' h' hcomm
  obtain ⟨c, hc, -⟩ := hU
  have e : (fun i => h'.f (v x i)) = fun i => (c.comp h₀).f (y x i) :=
    congrArg (fun k : Hom Q Q' => fun i => k.f (y x i)) hc.2.symm
  have e' : (fun i => (c.comp h₀).f (y x i)) = fun i => c.f (z x i) := by
    funext i
    exact congrArg c.f (hy x i)
  exact calc (fun i => h'.f (v x i)) = fun i => c.f (z x i) := e.trans e'
    _ = fun i => c.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
        congrArg (fun w : Fin d → Q₀.A => fun i => c.f (w i)) (hzx x)
    _ = (S.ε (c.comp (h₀.comp g)) (c.comp (a₀.comp f))).mulVec fun i => c.f (a₀.f (u x i)) :=
        map_mulVec S c _ _ _
    _ = (S.ε ((c.comp h₀).comp g) ((c.comp a₀).comp f)).mulVec fun i => (c.comp a₀).f (u x i) :=
        congrArg₂ (fun k k' => (S.ε k k').mulVec fun i => c.f (a₀.f (u x i)))
          (comp_assoc c h₀ g).symm (comp_assoc c a₀ f).symm
    _ = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) :=
        congrArg₂ (fun (k : Hom Q Q') (k' : Hom C Q') => (S.ε (k.comp g) (k'.comp f)).mulVec fun i => k'.f (u x i))
          hc.2 hc.1

end GlobalTheory.BSP.SiteCoord
