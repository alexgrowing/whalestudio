import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourUniq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.HeisSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem half_div {e : AE D} {k : ℕ} (hk : 0 < k) {s : WO S T} (hs : IsHalf e s) :
    ∃ t, IsHalf e t ∧ k • t = s := by
  refine ⟨s.map (fun a => algebraMap D.host.F (AE D) (k : D.host.F)⁻¹ * a), fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hs i j]
  · ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul, ← mul_assoc]
    have h1 : (k : AE D) * algebraMap D.host.F (AE D) (k : D.host.F)⁻¹ = 1 := by
      rw [show (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) by simp, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
    rw [h1, one_mul]

theorem symplO_off {e : AE D} (he : e * cA D e = 0) {u a : WO S T} (hu : ∀ i j, (e + cA D e) * u i j = 0)
    (ha : IsHalf e a) : symplO S T u a = 0 := by
  have hz : ∀ i j c d, incA D (S.gram⁻¹ i j) * cA D (a c j) * incA D (T.gram c d) * u d i = 0 := by
    intro i j c d
    have h1 : cA D (a c j) = cA D e * cA D (a c j) := by rw [← map_mul, ha c j]
    have h2 : cA D e * u d i + e * u d i = 0 := by
      rw [← add_mul, add_comm]
      exact hu d i
    linear_combination (incA D (S.gram⁻¹ i j) * incA D (T.gram c d) * u d i -
        incA D (S.gram⁻¹ i j) * incA D (T.gram c d) * e * u d i) * h1 +
      (incA D (S.gram⁻¹ i j) * cA D (a c j) * incA D (T.gram c d)) * h2 -
      (incA D (S.gram⁻¹ i j) * cA D (a c j) * incA D (T.gram c d) * u d i) * he
  simp [symplO, hO, hz]

theorem heisO_comm_of {u a : WO S T} (h : symplO S T u a = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T a f) = heisO ψ S T a (heisO ψ S T u f) := by
  have := congrArg (fun Tm : Module.End ℂ (WO S T → ℂ) => Tm f) (heisL_comm ψ S T u a)
  simpa [Module.End.mul_apply, heisL_apply, h] using this

open Classical in

theorem placeModel_core (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T))
    (f₀ : WO S T → ℂ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hdX : ∀ x, IsHalf e₁ x → (∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoX : ∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hvX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u f₀ = f₀)
    (hvY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm ∧
      (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm' → ∀ Φ, IsSBHalf e₁ Λ Φ → Tm' Φ = Tm Φ) ∧
      (∀ Φ, IsSBHalf e₁ Λ Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
      ∀ Φ, IsSBHalf e₁ Λ Φ → ∀ u : WO S T, (∀ a, IsHalf e₁ a → symplO S T u a = 0) →
        (∀ y, IsHalf (cA D e₁) y → symplO S T u y = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨Tm, hTm, -⟩ := exists_placeModel ψ S T e₁ he Λ f₀ hLL hdY hfX hfY hoX hoY hvX hvY

  have hχl : ∀ t t' y : WO S T, ψ (symplO S T (t + t') y) = ψ (symplO S T t y) * ψ (symplO S T t' y) := fun t t' y => by
    simp only [symplO_add_left, AddChar.map_add_eq_mul]
  have hχr : ∀ t y y' : WO S T, ψ (symplO S T t (y + y')) = ψ (symplO S T t y) * ψ (symplO S T t y') := fun t y y' => by
    simp only [symplO_add_right, AddChar.map_add_eq_mul]
  have hχ0 : ∀ t y : WO S T, ψ (symplO S T t y) ≠ 0 := fun t y => psi_ne_zero ψ _
  have hLL' : ∀ x ∈ Λ ⊓ halfSub S T e₁, ∀ y ∈ Λ ⊓ halfSub S T (cA D e₁), ψ (symplO S T x y) = 1 :=
    fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2
  have hdX' : ∀ x ∈ halfSub S T e₁, (∀ y ∈ Λ ⊓ halfSub S T (cA D e₁), ψ (symplO S T x y) = 1) → x ∈ Λ :=
    fun x hx h => hdX x hx fun y hy hye => h y (AddSubgroup.mem_inf.2 ⟨hy, hye⟩)
  have hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ halfSub S T e₁, ∃ t ∈ halfSub S T e₁, k • t = s := fun k hk s hs => by
    obtain ⟨t, ht, hts⟩ := half_div S T hk hs
    exact ⟨t, ht, hts⟩
  have hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ halfSub S T (cA D e₁), ∃ t ∈ halfSub S T (cA D e₁), k • t = s :=
    fun k hk s hs => by
      obtain ⟨t, ht, hts⟩ := half_div S T hk hs
      exact ⟨t, ht, hts⟩
  have hfinX : ∀ k, 0 < k → Finite (Four.Qt k (Λ ⊓ halfSub S T e₁)) := fun k hk => by
    obtain ⟨R, hR⟩ := hfX k hk
    exact finite_qt_of S T R fun u hu => by
      obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
      exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩
  have hfinY : ∀ k, 0 < k → Finite (Four.Qt k (Λ ⊓ halfSub S T (cA D e₁))) := fun k hk => by
    obtain ⟨R, hR⟩ := hfY k hk
    exact finite_qt_of S T R fun u hu => by
      obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
      exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩
  have htf : ∀ k : ℕ, 0 < k → ∀ t : WO S T, k • t = 0 → t = 0 := fun k hk t h => nsmul_eq_zero_WO S T hk h

  have abs : ∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm' →
      (∀ Φ, Four.IsSB Λ (halfSub S T e₁) Φ → ∀ x ∈ halfSub S T e₁,
        Tm' (fun t => Φ (t + x)) = heisL ψ S T x (Tm' Φ)) ∧
      (∀ Φ, Four.IsSB Λ (halfSub S T e₁) Φ → ∀ y ∈ halfSub S T (cA D e₁),
        Tm' (fun t => ψ (symplO S T t y) * Φ t) = heisL ψ S T y (Tm' Φ)) ∧
      Tm' (fun t => if t ∈ Λ ∧ t ∈ halfSub S T e₁ then (1 : ℂ) else 0) = f₀ := by
    intro Tm' h'
    refine ⟨fun Φ hΦ x hx => h'.trans Φ ((isSBHalf_iff S T).2 hΦ) x hx,
      fun Φ hΦ y hy => h'.modul Φ ((isSBHalf_iff S T).2 hΦ) y hy, ?_⟩
    have := h'.vac
    rw [one_smul] at this
    exact this
  obtain ⟨htr, hmo, hva⟩ := abs Tm hTm
  have hspan : ∀ Φ, IsSBHalf e₁ Λ Φ → Tm Φ ∈ Submodule.span ℂ
      {v | ∃ a ∈ halfSub S T e₁, ∃ y ∈ halfSub S T (cA D e₁), v = heisL ψ S T a (heisL ψ S T y f₀)} :=
    fun Φ hΦ => Four.model_mem_span hχl hχr hχ0 hLL' hdX' hdivX hdivY hfinX hfinY htf Tm htr hmo hva
      ((isSBHalf_iff S T).1 hΦ)
  refine ⟨Tm, hTm, fun Tm' h' Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ hΦ u hua huy hu0 => ?_⟩
  · obtain ⟨htr', hmo', hva'⟩ := abs Tm' h'
    exact Four.model_unique hχl hχr hχ0 hLL' hdX' hdivX hdivY hfinX hfinY htf Tm Tm' htr hmo hva htr' hmo' hva'
      ((isSBHalf_iff S T).1 hΦ)
  · have hzero : IsThetaFunO ψ S T 0 := by
      have := Formalism.IndefR.Eqv.thetaO_smul (0 : ℂ) hf₀
      rwa [zero_smul] at this
    have hmem := hspan Φ hΦ
    generalize Tm Φ = v₀ at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, -, y, -, rfl⟩ := hv
      exact heisStable ψ hψ S T a _ (heisStable ψ hψ S T y f₀ hf₀)
    | zero => exact hzero
    | add v w _ _ hv hw => exact Formalism.IndefR.Eqv.thetaO_add hv hw
    | smul c v _ hv => exact Formalism.IndefR.Eqv.thetaO_smul c hv
  · have hmem := hspan Φ hΦ
    generalize Tm Φ = v₀ at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hv
      simp only [heisL_apply]
      rw [heisO_comm_of ψ S T (hua a ha), heisO_comm_of ψ S T (huy y hy), hu0]
    | zero =>
      funext w
      simp [heisO]
    | add v w _ _ hv hw =>
      have := (heisL ψ S T u).map_add v w
      rw [heisL_apply, heisL_apply, heisL_apply] at this
      rw [this, hv, hw]
    | smul c v _ hv =>
      have := (heisL ψ S T u).map_smul c v
      rw [heisL_apply, heisL_apply] at this
      rw [this, hv]

theorem placeModelAt_of {D : D7} (h : PlaceLatDual D) : PlaceModelAt D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he f₀ hf₀ hvac e₁ he₁
  obtain ⟨-, -, hP⟩ := h ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, hd3, hfin, hop⟩ := hP P e he
  have hcc : cA D (cA D e) = e := cA_cA e
  have vacE : ∀ u ∈ latAll S T ΛS ΛT, IsHalf e u → heisO ψ S T u f₀ = f₀ := fun u hu h' => hvac u hu (Or.inl h')
  have vacC : ∀ u ∈ latAll S T ΛS ΛT, IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀ :=
    fun u hu h' => hvac u hu (Or.inr h')
  have offE : ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) → ∀ a, IsHalf e a → symplO S T u a = 0 :=
    fun u hu a ha => symplO_off S T he.2 hu ha
  have offC : ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) → ∀ a, IsHalf (cA D e) a → symplO S T u a = 0 :=
    fun u hu a ha => symplO_off S T (cA_half_orth he.2) (fun i j => by rw [hcc, add_comm]; exact hu i j) ha
  rcases he₁ with rfl | rfl
  · obtain ⟨Tm, h1, h2, h3, h4⟩ := placeModel_core ψ S T hψ e₁ he.2 (latAll S T ΛS ΛT) f₀ hf₀
      (fun x hx hxe y hy hye => (hd2 y hye).2 hy x hx hxe)
      (fun y hye h' => (hd2 y hye).1 h')
      (fun x hxe h' => (hd3 x hxe).1 h')
      (fun k hk => hfin k hk e₁ (Or.inl rfl)) (fun k hk => hfin k hk (cA D e₁) (Or.inr rfl))
      (fun x hx => hop e₁ (Or.inl rfl) x hx) (fun y hy => hop (cA D e₁) (Or.inr rfl) y hy)
      vacE vacC
    exact ⟨Tm, h1, h2, h3, fun Φ hΦ u hu hu0 => h4 Φ hΦ u (offE u hu) (offC u hu) hu0⟩
  · obtain ⟨Tm, h1, h2, h3, h4⟩ := placeModel_core ψ S T hψ (cA D e) (cA_half_orth he.2) (latAll S T ΛS ΛT) f₀ hf₀
      (by
        rw [hcc]
        intro x hx hxe y hy hye
        rw [symplO_swap S T y x]
        exact psi_neg_one ψ ((hd2 x hxe).2 hx y hy hye))
      (by
        rw [hcc]
        intro y hye h'
        refine (hd3 y hye).1 fun y' hy' hy'e => ?_
        have := psi_neg_one ψ (h' y' hy' hy'e)
        rwa [symplO_swap S T y y', neg_neg] at this)
      (by
        rw [hcc]
        intro x hxe h'
        refine (hd2 x hxe).1 fun y hy hye => ?_
        have := psi_neg_one ψ (h' y hy hye)
        rwa [← symplO_swap S T x y] at this)
      (fun k hk => hfin k hk (cA D e) (Or.inr rfl))
      (by rw [hcc]; exact fun k hk => hfin k hk e (Or.inl rfl))
      (fun x hx => hop (cA D e) (Or.inr rfl) x hx)
      (by rw [hcc]; exact fun y hy => hop e (Or.inl rfl) y hy)
      vacC
      (by rw [hcc]; exact vacE)
    refine ⟨Tm, h1, h2, h3, fun Φ hΦ u hu hu0 => h4 Φ hΦ u (offC u hu) ?_ hu0⟩
    rw [hcc]
    exact offE u hu

end Formalism.IndefR.Fin

end
