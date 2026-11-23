import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Map
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

theorem d_cup_one (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a m : ℕ} (h : 1 + a = m) (y : CH.Cn F₂ a) :
    CH.d F₃ m (P.cupC h b y) = -P.cupC (by omega : 1 + (a + 1) = m + 1) b (CH.d F₂ a y) := by
  rw [CrystallineSemistableComparison.P.leibniz, hb]
  simp

def cupMap (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) (a : ℕ) :
    CH.H F₂ a →ₗ[R] CH.H F₃ (a + 1) :=
  Submodule.mapQ _ _ ((((P.cupC (Nat.add_comm 1 a) b).comp (Submodule.subtype _))).codRestrict _ fun y => by
    change CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y.1) = 0
    rw [d_cup_one P b hb]
    have : CH.d F₂ a y.1 = 0 := y.2
    rw [this, map_zero, neg_zero]) (by
      intro y hy
      change P.cupC (Nat.add_comm 1 a) b y.1 ∈ (CH.cx F₃).B (a + 1)
      have hy' : y.1 ∈ (CH.cx F₂).B a := hy
      cases a with
      | zero =>
        have : y.1 = 0 := hy'
        rw [this, map_zero]
        exact Submodule.zero_mem _
      | succ m =>
        obtain ⟨t, ht⟩ := hy'
        refine ⟨-P.cupC (Nat.add_comm 1 m) b t, ?_⟩
        change CH.d F₃ _ _ = _
        rw [map_neg, d_cup_one P b hb, neg_neg]
        change P.cupC _ b (CH.d F₂ m t) = _
        exact congrArg _ ht)

theorem cupMap_cls (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a : ℕ} (y : CH.Cn F₂ a)
    (hy : CH.d F₂ a y = 0) (hz : CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y) = 0) :
    cupMap P b hb a ((CH.cx F₂).cls y hy) = (CH.cx F₃).cls (P.cupC (Nat.add_comm 1 a) b y) hz := rfl

def castH (F : C ⥤ ModuleCat.{0} R) {W W' : ObjectProperty C} (h : W = W') (j : ℕ) : HU F W' j ≃ₗ[R] HU F W j := by
  subst h
  exact LinearEquiv.refl R _

end Map

section Sch
variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem append_cons {M : Type*} {a : ℕ} (t : M) (g : Fin a → M) :
    Fin.append ![t] g ∘ Fin.cast (Nat.add_comm 1 a).symm = (Fin.cons t g : Fin (a + 1) → M) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · have e : Fin.cast (Nat.add_comm 1 a).symm (0 : Fin (a + 1)) = Fin.castAdd a (0 : Fin 1) := Fin.ext (by simp)
    simp only [Function.comp, e, Fin.append_left, Fin.cons_zero]
    rfl
  · have e : Fin.cast (Nat.add_comm 1 a).symm k.succ = Fin.natAdd 1 k := Fin.ext (by simp [Nat.add_comm])
    simp only [Function.comp, e, Fin.append_right, Fin.cons_succ]

theorem form_cup' (hFC : FormCup) {a c : ℕ} (hc : 1 + a = c) (g₁ g₀ : Sec q V) (t : Sec q V) (g : Fin a → Sec q V)
    (x : CH.Cn ((inU q V).ι ⋙ G q 1) 1) (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hx : CH.d _ 1 x = 0) (hy : CH.d _ a y = 0)
    (h₁ : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls x hx)) (h₂ : IsForm q V g₀ g ((CH.cx _).cls y hy)) :
    ∃ hz, IsForm q V (a := c) (g₁ * g₀) (Fin.append ![t] g ∘ Fin.cast hc.symm)
      ((CH.cx ((inU q V).ι ⋙ G q c)).cls (cupU q (inU q V) hc hc x y) hz) := by
  subst hc
  exact hFC K Z q V 1 a g₁ g₀ ![t] g x y hx hy h₁ h₂

theorem cup_form (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V) (b : CH.Cn ((inU q V).ι ⋙ G q 1) 1)
    (hb : CH.d _ 1 b = 0) (hf : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls b hb))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = E₂ ω)
    (hz : CH.d ((inU q V).ι ⋙ G q (a + 1)) (a + 1) (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) = 0) :
    (CH.cx ((inU q V).ι ⋙ G q (a + 1))).cls (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) hz =
      E₃ (g₁ • w ω) := by
  let P := pairU (grOk (smFun Z q) (Nat.add_comm 1 a)).pair (inU q V)
  have key : (cupMap P b hb a).restrictScalars K ∘ₗ E₂ = E₃ ∘ₗ ((g₁ • w).restrictScalars K) := by
    refine lin_ext hFL _ _ fun g₀ v => ?_
    obtain ⟨⟨y', hy'⟩, hyy⟩ := Submodule.Quotient.mk_surjective _ (E₂ (form K g₀ v))
    have hy'' : CH.d _ a y' = 0 := hy'
    have hc' : (CH.cx _).cls y' hy'' = E₂ (form K g₀ v) := hyy
    have hI := h₂ g₀ v
    rw [← hc'] at hI
    obtain ⟨hz', hform⟩ := form_cup' hFC (Nat.add_comm 1 a) g₁ g₀ t v b y' hb hy'' hf hI
    rw [append_cons] at hform
    have hu := ((hFU K Z q V).2 (a + 1) (g₁ * g₀) (Fin.cons t v)).unique hform (h₃ _ _)
    change cupMap P b hb a (E₂ (form K g₀ v)) = E₃ (g₁ • w (form K g₀ v))
    rw [← hc', hw]
    refine (cupMap_cls P b hb y' hy'' hz').trans (hu.trans ?_)
    congr 1
    exact mul_smul _ _ _
  have := LinearMap.congr_fun key ω
  change cupMap P b hb a (E₂ ω) = E₃ (g₁ • w ω) at this
  rw [← hcls] at this
  exact (cupMap_cls P b hb y hy hz).symm.trans this

end Sch

end GlobalTheory.CompanionTheory.RelKill
