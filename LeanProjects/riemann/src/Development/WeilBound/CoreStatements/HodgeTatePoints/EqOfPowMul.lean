import Development.WeilBound.CoreStatements.HodgeTatePoints.ReProd
import Development.WeilBound.CoreStatements.HodgeTatePoints.CntCoord
import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedAFStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Re

def splitEquiv {N N₁ N₂ : Type} [AddCommGroup N] [AddCommGroup N₁] [AddCommGroup N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) : N₁ × N₂ ≃+ N where
  toFun z := ι₁ z.1 + ι₂ z.2
  invFun x := (π₁ x, π₂ x)
  left_inv z := by simp [h11, h22, h12, h21]
  right_inv x := hsum x
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel

theorem ret_colen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
    {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) (hs₁ : ∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier)
    (a b : NNReal)
    (ha : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))) a)
    (hb : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))) b) :
    HasColen R v AA.carrier (a ^ Fintype.card N₂ * b ^ Fintype.card N₁) := by
  let e := splitEquiv ι₁ π₁ ι₂ π₂ h11 h22 hsum h12 h21
  have e1 : (fun y : N₁ => e (y, 0)) = ι₁ := by
    funext y
    show ι₁ y + ι₂ 0 = ι₁ y
    simp
  have e2 : (fun y : N₂ => e (0, y)) = ι₂ := by
    funext y
    show ι₁ 0 + ι₂ y = ι₂ y
    simp
  have h := tn_char AA e (fun g hg => by
    convert hs₁ g hg using 3 with x
    exact congrFun e1 _)
  rw [e1, e2] at h
  have h2 := hasColen_tn ha hb
  rw [← h] at h2
  have h3 := hasColen_map v e.symm _ _ h2
  rwa [show AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
    AA.carrier.map (pbE (C := C) (R := R) e : (N → C) →ₗ[R] (N₁ × N₂ → C)) from rfl,
    map_pbE_symm] at h3

theorem eq_of_pow_mul {x₁ y₁ x₂ y₂ : NNReal} {m n : ℕ} (hm : m ≠ 0) (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (hy : y₂ ≠ 0) (h : x₁ ^ m * x₂ ^ n = y₁ ^ m * y₂ ^ n) : x₁ = y₁ := by
  refine le_antisymm h₁ (not_lt.1 fun hlt => ?_)
  have a : x₁ ^ m < y₁ ^ m := pow_lt_pow_left₀ hlt zero_le hm
  have b : x₂ ^ n ≤ y₂ ^ n := pow_le_pow_left₀ zero_le h₂ n
  have c : 0 < y₂ ^ n := pow_pos (pos_iff_ne_zero.2 hy) n
  exact absurd h (ne_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b zero_le)
    (mul_lt_mul_of_pos_right a c)))

theorem ret_tight : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA N' _ _ _ ι π hπ hst hT
  classical
  have hcnt := @PositivityTheory.HtPt.Ra.cnt
  have hlens := @PositivityTheory.HtPt.Rc.lens
  let ι₂ : π.ker →+ N := π.ker.subtype
  let π₂ : N →+ π.ker := (AddMonoidHom.id N - ι.comp π).codRestrict π.ker (fun x => by
    simp [AddMonoidHom.mem_ker, hπ])
  have hπ₂ : ∀ x, ι₂ (π₂ x) = x - ι (π x) := fun _ => rfl
  have h12 : ∀ y, π (ι₂ y) = 0 := fun y => y.2
  have h22 : ∀ y, π₂ (ι₂ y) = y := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι₂ y)) = ι₂ y
    rw [hπ₂, h12]; simp)
  have h21 : ∀ y, π₂ (ι y) = 0 := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι y)) = 0
    rw [hπ₂, hπ]; simp)
  have hsum : ∀ x, ι (π x) + ι₂ (π₂ x) = x := fun x => by rw [hπ₂]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier :=
    (stabadd C R N N AA AA (AddMonoidHom.id N) (ι.comp π) (fun g hg => hg) hst).2
  obtain ⟨⟨A₁, hA₁⟩, -⟩ := ret_hopf p C v R hv hp N AA N' ι π hπ hst
  obtain ⟨⟨A₂, hA₂⟩, -⟩ := ret_hopf p C v R hv hp N AA π.ker ι₂ π₂ h22 hs₂
  have hN₁ : ∀ y : N', p • y = 0 := fun y => by rw [← hπ y, ← map_nsmul, hN, map_zero]
  have hN₂ : ∀ y : π.ker, p • y = 0 := fun y => by rw [← h22 y, ← map_nsmul, hN, map_zero]
  obtain ⟨a₁, c₁, o₁, -, hc₁0, -, ha₁, hc₁, ho₁⟩ := hlens p C v R hv hp N' hN₁ A₁
  obtain ⟨a₂, c₂, o₂, -, hc₂0, ho₂0, ha₂, hc₂, ho₂⟩ := hlens p C v R hv hp π.ker hN₂ A₂
  have l₁ := (hcnt p C v R hv hp N' hN₁ A₁ _ _ ha₁ hc₁).1
  have l₂ := (hcnt p C v R hv hp π.ker hN₂ A₂ _ _ ha₂ hc₂).1
  have m₁ := u4 p C v R hv hp N' hN₁ A₁ _ _ hc₁ ho₁
  have m₂ := u4 p C v R hv hp π.ker hN₂ A₂ _ _ hc₂ ho₂
  rw [hA₁] at ha₁ hc₁ ho₁
  rw [hA₂] at ha₂ hc₂ ho₂
  obtain ⟨a, c, o, ha, hc, ho, ea, eo⟩ := hT
  obtain rfl := hasLen_unique hv ha
    (ret_af p C v R hv hp N AA N' π.ker ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ha₁ ha₂)
  obtain rfl := hasLen_unique hv ho
    (ret_om hv AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ho₁ ho₂)
  obtain rfl := hasColen_unique hv AA.lat hc
    (ret_colen AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst _ _ hc₁ hc₂)
  have hcard : Fintype.card N = Fintype.card N' * Fintype.card π.ker := by
    rw [← Fintype.card_prod]
    exact (Fintype.card_congr (splitEquiv ι π ι₂ π₂ hπ h22 hsum h12 h21).toEquiv).symm
  rw [hcard] at ea eo
  refine ⟨a₁, c₁, o₁, ha₁, hc₁, ho₁, ?_, ?_⟩
  · refine eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      l₁ l₂ (pow_ne_zero _ hc₂0) ?_
    calc _ = (a₁ * a₂) ^ (Fintype.card N' * Fintype.card π.ker * (p - 1)) := by ring
      _ = _ := by rw [ea]; ring
  · refine (eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      m₁ m₂ (pow_ne_zero _ ho₂0) ?_).symm
    calc _ = (c₁ ^ Fintype.card π.ker * c₂ ^ Fintype.card N') ^ 2 := by ring
      _ = _ := by rw [← eo]; ring

end PositivityTheory.HtPt.Re
