import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ReesBasis

open scoped Classical

variable {Λ : Type} [CommRing Λ] {C : Type 1} [Category.{0} C] {F : C ⥤ ModuleCat.{0} Λ} (Φ : Flt F)
  {T₁ T₂ : C} {ι : Type} (e : (ι →₀ F.obj T₁) ≃ₗ[Λ] F.obj T₂)
  (he : ∀ r z, e z ∈ (Φ.S r).S T₂ ↔ ∀ a, z a ∈ (Φ.S r).S T₁)

include he in

theorem coord_mem (r : ℕ) (w : F.obj T₂) (hw : w ∈ (Φ.S r).S T₂) (a : ι) : e.symm w a ∈ (Φ.S r).S T₁ :=
  (he r _).1 (by simpa using hw) a

include he in

theorem filt_mem (p : ι → Prop) (r : ℕ) (w : F.obj T₂) (hw : w ∈ (Φ.S r).S T₂) :
    e (Finsupp.filter p (e.symm w)) ∈ (Φ.S r).S T₂ := by
  refine (he r _).2 fun a => ?_
  by_cases ha : p a
  · rw [Finsupp.filter_apply_pos _ _ ha]
    exact coord_mem Φ e he r w hw a
  · rw [Finsupp.filter_apply_neg _ _ ha]
    exact zero_mem _

def co (a : ι) : Φ.Pr T₂ →ₗ[ℤ[X]] Φ.Pr T₁ :=
  Flt.lin
    { toFun := fun x r => ⟨e.symm (x r).1 a, coord_mem Φ e he r _ (x r).2 a⟩
      map_zero' := funext fun r => Subtype.ext (show e.symm (0 : F.obj T₂) a = 0 by simp)
      map_add' := fun x y => funext fun r => Subtype.ext
        (show e.symm ((x r).1 + (y r).1) a = e.symm (x r).1 a + e.symm (y r).1 a by simp) } fun x => by
    rw [Flt.X_smul, Flt.X_smul]
    funext r
    cases r with
    | zero => exact Subtype.ext (show e.symm (0 : F.obj T₂) a = 0 by simp)
    | succ n => exact Subtype.ext (show e.symm (Φ.μ • (x n).1) a = Φ.μ • e.symm (x n).1 a by simp)

def fl (p : ι → Prop) : Φ.Pr T₂ →ₗ[ℤ[X]] Φ.Pr T₂ :=
  Flt.lin
    { toFun := fun x r => ⟨e (Finsupp.filter p (e.symm (x r).1)), filt_mem Φ e he p r _ (x r).2⟩
      map_zero' := funext fun r => Subtype.ext
        (show e (Finsupp.filter p (e.symm (0 : F.obj T₂))) = 0 by simp [Finsupp.filter_zero])
      map_add' := fun x y => funext fun r => Subtype.ext
        (show e (Finsupp.filter p (e.symm ((x r).1 + (y r).1))) =
          e (Finsupp.filter p (e.symm (x r).1)) + e (Finsupp.filter p (e.symm (y r).1)) by
            simp [Finsupp.filter_add]) } fun x => by
    rw [Flt.X_smul, Flt.X_smul]
    funext r
    cases r with
    | zero => exact Subtype.ext (show e (Finsupp.filter p (e.symm (0 : F.obj T₂))) = 0 by simp [Finsupp.filter_zero])
    | succ n =>
      refine Subtype.ext (show e (Finsupp.filter p (e.symm (Φ.μ • (x n).1))) =
        Φ.μ • e (Finsupp.filter p (e.symm (x n).1)) from ?_)
      rw [← map_smul]
      congr 1
      ext a
      by_cases ha : p a <;> simp [Finsupp.filter_apply, ha]

theorem fl_coe (p : ι → Prop) (x : Φ.Pr T₂) (r : ℕ) :
    (fl Φ e he p x r).1 = e (Finsupp.filter p (e.symm (x r).1)) := rfl

omit he in

theorem diag {φ₂ : T₂ ⟶ T₂} {φ₁ : T₁ ⟶ T₁} {c : ι → Λ}
    (hd : ∀ a m, (F.map φ₂).hom (e (Finsupp.single a m)) = e (Finsupp.single a (c a • (F.map φ₁).hom m)))
    (w : F.obj T₂) (a : ι) : e.symm ((F.map φ₂).hom w) a = c a • (F.map φ₁).hom (e.symm w a) := by
  obtain ⟨z, rfl⟩ := e.surjective w
  rw [e.symm_apply_apply]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, smul_add, hf, hg]
  | single b m =>
    rw [hd, e.symm_apply_apply]
    by_cases h : b = a
    · subst h; simp
    · simp [Finsupp.single_apply, h]

theorem co_nat {φ₂ : T₂ ⟶ T₂} {φ₁ : T₁ ⟶ T₁} {c : ι → Λ}
    (hd : ∀ a m, (F.map φ₂).hom (e (Finsupp.single a m)) = e (Finsupp.single a (c a • (F.map φ₁).hom m)))
    (a : ι) (h1 : c a = 1) (x : Φ.Pr T₂) :
    co Φ e he a (Φ.prMap φ₂ x) = Φ.prMap φ₁ (co Φ e he a x) := by
  funext r
  refine Subtype.ext (show e.symm ((F.map φ₂).hom (x r).1) a = (F.map φ₁).hom (e.symm (x r).1 a) from ?_)
  rw [diag e hd, h1, one_smul]

theorem fl_nat {φ₂ : T₂ ⟶ T₂} {φ₁ : T₁ ⟶ T₁} {c : ι → Λ}
    (hd : ∀ a m, (F.map φ₂).hom (e (Finsupp.single a m)) = e (Finsupp.single a (c a • (F.map φ₁).hom m)))
    (p : ι → Prop) (x : Φ.Pr T₂) :
    fl Φ e he p (Φ.prMap φ₂ x) = Φ.prMap φ₂ (fl Φ e he p x) := by
  funext r
  refine Subtype.ext (show e (Finsupp.filter p (e.symm ((F.map φ₂).hom (x r).1))) =
    (F.map φ₂).hom (e (Finsupp.filter p (e.symm (x r).1))) from ?_)
  apply e.symm.injective
  rw [e.symm_apply_apply]
  ext a
  rw [diag e hd, e.symm_apply_apply]
  by_cases ha : p a
  · rw [Finsupp.filter_apply_pos _ _ ha, Finsupp.filter_apply_pos _ _ ha, diag e hd]
  · rw [Finsupp.filter_apply_neg _ _ ha, Finsupp.filter_apply_neg _ _ ha]; simp

theorem co_th {a₀ : ι} {t : T₁ ⟶ T₂} (ht : ∀ m, e (Finsupp.single a₀ m) = (F.map t).hom m) (y : Φ.Pr T₁) :
    co Φ e he a₀ (Φ.prMap t y) = y := by
  funext r
  refine Subtype.ext (show e.symm ((F.map t).hom (y r).1) a₀ = (y r).1 from ?_)
  rw [← ht, e.symm_apply_apply]; simp

theorem fl_th {a₀ : ι} {t : T₁ ⟶ T₂} (ht : ∀ m, e (Finsupp.single a₀ m) = (F.map t).hom m)
    {p : ι → Prop} (hp : ¬ p a₀) (y : Φ.Pr T₁) : fl Φ e he p (Φ.prMap t y) = 0 := by
  funext r
  refine Subtype.ext (show e (Finsupp.filter p (e.symm ((F.map t).hom (y r).1))) = 0 from ?_)
  rw [← ht, e.symm_apply_apply, Finsupp.filter_single_of_neg _ hp, map_zero]

theorem fl_idem (p : ι → Prop) (x : Φ.Pr T₂) : fl Φ e he p (fl Φ e he p x) = fl Φ e he p x := by
  funext r
  refine Subtype.ext (show e (Finsupp.filter p (e.symm (e (Finsupp.filter p (e.symm (x r).1))))) =
    e (Finsupp.filter p (e.symm (x r).1)) from ?_)
  rw [e.symm_apply_apply]
  congr 1
  ext a
  by_cases ha : p a <;> simp [Finsupp.filter_apply, ha]

theorem fl_orth {p q : ι → Prop} (h : ∀ a, p a → ¬ q a) (x : Φ.Pr T₂) :
    fl Φ e he q (fl Φ e he p x) = 0 := by
  funext r
  refine Subtype.ext (show e (Finsupp.filter q (e.symm (e (Finsupp.filter p (e.symm (x r).1))))) = 0 from ?_)
  rw [e.symm_apply_apply]
  convert map_zero e
  ext a
  by_cases ha : p a
  · simp [Finsupp.filter_apply, ha, h a ha]
  · by_cases hb : q a <;> simp [Finsupp.filter_apply, ha, hb]

def ev (T : C) (r : ℕ) : Φ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fl_sum {d : ℕ} {a₀ : ι} {t : T₁ ⟶ T₂} (ht : ∀ m, e (Finsupp.single a₀ m) = (F.map t).hom m)
    (K : ι → Option (Fin d)) (hK : ∀ a, K a = none → a = a₀) (hK₀ : K a₀ = none) (x : Φ.Pr T₂) :
    Φ.prMap t (co Φ e he a₀ x) + ∑ k, fl Φ e he (fun a => K a = some k) x = x := by
  funext r
  refine Subtype.ext ?_
  have h1 : ((∑ k, fl Φ e he (fun a => K a = some k) x) r).1 =
      ∑ k, (fl Φ e he (fun a => K a = some k) x r).1 :=
    map_sum (ev Φ T₂ r) (fun k => fl Φ e he (fun a => K a = some k) x) Finset.univ
  simp only [fl_coe] at h1
  refine (show ((Φ.prMap t (co Φ e he a₀ x)) r).1 + ((∑ k, fl Φ e he (fun a => K a = some k) x) r).1 = (x r).1 from ?_)
  rw [h1, show ((Φ.prMap t (co Φ e he a₀ x)) r).1 = (F.map t).hom (e.symm (x r).1 a₀) from rfl, ← ht, ← map_sum, ← map_add]
  apply e.symm.injective
  rw [e.symm_apply_apply]
  ext a
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
  cases hKa : K a with
  | none =>
    obtain rfl := hK a hKa
    simp [Finsupp.filter_apply, hKa]
  | some k₀ =>
    have hne : a₀ ≠ a := by rintro rfl; simp [hK₀] at hKa
    simp [Finsupp.filter_apply, hKa, Finsupp.single_apply, hne]

theorem fl_fix {p : ι → Prop} {x : Φ.Pr T₂} (h : fl Φ e he p x = x) (r : ℕ) (a : ι) (ha : ¬ p a) :
    e.symm (x r).1 a = 0 := by
  have h1 : e (Finsupp.filter p (e.symm (x r).1)) = (x r).1 := congrArg (fun y : Φ.Pr T₂ => (y r).1) h
  rw [← h1, e.symm_apply_apply, Finsupp.filter_apply_neg _ _ ha]

theorem solve {φ₁ : T₁ ⟶ T₁} {c : ι → Λ} {p : ι → Prop}
    (hs : ∀ a, p a → ∀ r, ∀ x ∈ (Φ.S r).S T₁, ∃ y ∈ (Φ.S (r + 1)).S T₁,
      c a • (F.map φ₁).hom y - y = Φ.μ • x)
    (r : ℕ) (z : ι →₀ F.obj T₁) (hz : ∀ a, z a ∈ (Φ.S r).S T₁) (hp : ∀ a, ¬ p a → z a = 0) :
    ∃ u : ι →₀ F.obj T₁, (∀ a, u a ∈ (Φ.S (r + 1)).S T₁) ∧ (∀ a, ¬ p a → u a = 0) ∧
      ∀ a, c a • (F.map φ₁).hom (u a) - u a = Φ.μ • z a := by
  have h : ∀ a, ∃ y ∈ (Φ.S (r + 1)).S T₁, (z a = 0 → y = 0) ∧ c a • (F.map φ₁).hom y - y = Φ.μ • z a := by
    intro a
    by_cases h0 : z a = 0
    · exact ⟨0, zero_mem _, fun _ => rfl, by simp [h0]⟩
    · have hpa : p a := by_contra fun hn => h0 (hp a hn)
      obtain ⟨y, hy, hy'⟩ := hs a hpa r _ (hz a)
      exact ⟨y, hy, fun h => absurd h h0, hy'⟩
  choose u hu hu0 hu1 using h
  refine ⟨Finsupp.onFinset z.support u fun a ha => ?_, hu, fun a ha => hu0 a (hp a ha), hu1⟩
  rw [Finsupp.mem_support_iff]
  exact fun h0 => ha (hu0 a h0)

theorem fl_surj {φ₂ : T₂ ⟶ T₂} {φ₁ : T₁ ⟶ T₁} {c : ι → Λ} {p : ι → Prop}
    (hd : ∀ a m, (F.map φ₂).hom (e (Finsupp.single a m)) = e (Finsupp.single a (c a • (F.map φ₁).hom m)))
    (hs : ∀ a, p a → ∀ r, ∀ x ∈ (Φ.S r).S T₁, ∃ y ∈ (Φ.S (r + 1)).S T₁,
      c a • (F.map φ₁).hom y - y = Φ.μ • x)
    (x : Φ.Pr T₂) (hx : fl Φ e he p x = x) :
    ∃ y, fl Φ e he p y = y ∧ Φ.prMap φ₂ y - y = (X : ℤ[X]) • x := by
  have h := fun r => solve Φ hs r (e.symm (x r).1) (coord_mem Φ e he r _ (x r).2)
    (fun a ha => fl_fix Φ e he hx r a ha)
  choose u hu hu0 hu1 using h
  let y : Φ.Pr T₂ := fun r => match r with
    | 0 => 0
    | r + 1 => ⟨e (u r), (he _ _).2 (hu r)⟩
  refine ⟨y, ?_, ?_⟩
  · funext r
    cases r with
    | zero => exact Subtype.ext (show e (Finsupp.filter p (e.symm (0 : F.obj T₂))) = 0 by simp [Finsupp.filter_zero])
    | succ n =>
      refine Subtype.ext (show e (Finsupp.filter p (e.symm (e (u n)))) = e (u n) from ?_)
      rw [e.symm_apply_apply]
      congr 1
      ext a
      by_cases ha : p a
      · rw [Finsupp.filter_apply_pos _ _ ha]
      · rw [Finsupp.filter_apply_neg _ _ ha, hu0 n a ha]
  · funext r
    cases r with
    | zero =>
      rw [Flt.X_smul_zero]
      exact Subtype.ext (show (F.map φ₂).hom (0 : F.obj T₂) - 0 = 0 by simp)
    | succ n =>
      refine Subtype.ext ?_
      rw [Flt.X_smul_succ]
      refine (show (F.map φ₂).hom (e (u n)) - e (u n) = Φ.μ • (x n).1 from ?_)
      apply e.symm.injective
      ext a
      have := hu1 n a
      rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, diag e hd, e.symm_apply_apply]
      exact this

theorem fl_inj {φ₂ : T₂ ⟶ T₂} {φ₁ : T₁ ⟶ T₁} {c : ι → Λ} {p : ι → Prop}
    (hd : ∀ a m, (F.map φ₂).hom (e (Finsupp.single a m)) = e (Finsupp.single a (c a • (F.map φ₁).hom m)))
    (hi : ∀ a, p a → ∀ x, c a • (F.map φ₁).hom x = x → Φ.μ • x = 0)
    (x : Φ.Pr T₂) (hx : fl Φ e he p x = x) (hg : Φ.prMap φ₂ x = x) : (X : ℤ[X]) • x = 0 := by
  funext r
  cases r with
  | zero => rw [Flt.X_smul_zero]; rfl
  | succ n =>
    refine Subtype.ext ?_
    rw [Flt.X_smul_succ]
    refine (show Φ.μ • (x n).1 = 0 from ?_)
    apply e.symm.injective
    ext a
    rw [map_smul, Finsupp.smul_apply, map_zero, Finsupp.zero_apply]
    by_cases ha : p a
    · refine hi a ha _ ?_
      rw [← diag e hd]
      exact congrArg (fun w => e.symm w a) (congrArg (fun y : Φ.Pr T₂ => (y n).1) hg)
    · rw [fl_fix Φ e he hx n a ha, smul_zero]

theorem main : ∀ {Λ : Type} [CommRing Λ] {C : Type 1} [Category.{0} C] {F : C ⥤ ModuleCat.{0} Λ} (Φ : Flt F) {d : ℕ} (ι₁ ι₂ : SingleObj (Gam d) ⥤ C) (θ : ι₁ ⟶ ι₂) {ι : Type} (a₀ : ι) (e : (ι →₀ F.obj (ι₁.obj (SingleObj.star _))) ≃ₗ[Λ] F.obj (ι₂.obj (SingleObj.star _))) (χ : Gam d → ι → Λ), (∀ m, e (Finsupp.single a₀ m) = (F.map (θ.app _)).hom m) → (∀ (g : Gam d) a m, (F.map (ι₂.map (X := SingleObj.star _) (Y := SingleObj.star _) g)).hom (e (Finsupp.single a m)) = e (Finsupp.single a (χ g a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) g)).hom m))) → (∀ g, χ g a₀ = 1) → (∀ r z, e z ∈ (Φ.S r).S _ ↔ ∀ a, z a ∈ (Φ.S r).S _) → (∀ a, a ≠ a₀ → ∃ k : Fin d, (∀ x, χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom x = x → Φ.μ • x = 0) ∧ ∀ r, ∀ x ∈ (Φ.S r).S _, ∃ y ∈ (Φ.S (r + 1)).S _, χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom y - y = Φ.μ • x) → Nonempty (NI (X : ℤ[X]) (Functor.whiskerRight θ Φ.rees)) := by
  intro Λ _ C _ F Φ d ι₁ ι₂ θ ι a₀ e χ h1 h2 h3 h4 h5
  have hK : ∀ a, ∃ o : Option (Fin d), (a = a₀ ∧ o = none) ∨ (a ≠ a₀ ∧ ∃ k, o = some k ∧
      (∀ x, χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom x = x → Φ.μ • x = 0) ∧
      ∀ r, ∀ x ∈ (Φ.S r).S _, ∃ y ∈ (Φ.S (r + 1)).S _,
        χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom y - y = Φ.μ • x) := by
    intro a
    by_cases ha : a = a₀
    · exact ⟨none, Or.inl ⟨ha, rfl⟩⟩
    · obtain ⟨k, hk⟩ := h5 a ha
      exact ⟨some k, Or.inr ⟨ha, k, rfl, hk⟩⟩
  choose K hK using hK
  have hKn : ∀ a, K a = none → a = a₀ := fun a h => by
    rcases hK a with h' | ⟨_, k, hk, _⟩
    · exact h'.1
    · simp [hk] at h
  have hK₀ : K a₀ = none := by
    rcases hK a₀ with h' | ⟨h', _⟩
    · exact h'.2
    · exact absurd rfl h'
  have hKs : ∀ a k, K a = some k →
      (∀ x, χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom x = x → Φ.μ • x = 0) ∧
      ∀ r, ∀ x ∈ (Φ.S r).S _, ∃ y ∈ (Φ.S (r + 1)).S _,
        χ (gen k) a • (F.map (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k))).hom y - y = Φ.μ • x := by
    intro a k h
    rcases hK a with h' | ⟨_, k', hk', h''⟩
    · simp [h'.2] at h
    · obtain rfl : k = k' := by simpa [h] using hk'
      exact h''
  let ρ : ι₂ ⋙ Φ.rees ⟶ ι₁ ⋙ Φ.rees :=
    { app := fun _ => ModuleCat.ofHom (co Φ e h4 a₀)
      naturality := fun _ _ g => ModuleCat.hom_ext (LinearMap.ext fun x =>
        co_nat Φ e h4 (h2 g) a₀ (h3 g) x) }
  let π : Fin d → (ι₂ ⋙ Φ.rees ⟶ ι₂ ⋙ Φ.rees) := fun k =>
    { app := fun _ => ModuleCat.ofHom (fl Φ e h4 (fun a => K a = some k))
      naturality := fun _ _ g => ModuleCat.hom_ext (LinearMap.ext fun x =>
        fl_nat Φ e h4 (h2 g) _ x) }
  refine ⟨{ ρ := ρ, π := π, αρ := ?_, sum := ?_, απ := ?_, idem := ?_, orth := ?_, surj := ?_, inj := ?_ }⟩
  · exact NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun y =>
      co_th Φ e h4 h1 y))
  · refine NatTrans.ext (funext fun X' => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    simp only [NatTrans.app_add, NatTrans.app_sum, ModuleCat.hom_add, ModuleCat.hom_sum,
      LinearMap.add_apply, LinearMap.sum_apply]
    exact fl_sum Φ e h4 h1 K hKn hK₀ x
  · intro k
    exact NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun y =>
      fl_th Φ e h4 h1 (by simp [hK₀]) y))
  · intro k
    exact NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun x =>
      fl_idem Φ e h4 _ x))
  · intro k k' hkk
    exact NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun x =>
      fl_orth Φ e h4 (fun a ha hb => hkk (by simpa [ha] using hb)) x))
  · intro k x hx
    exact fl_surj Φ e h4 (h2 (gen k)) (fun a ha => (hKs a k ha).2) x hx
  · intro k x hx hg
    exact fl_inj Φ e h4 (h2 (gen k)) (fun a ha => (hKs a k ha).1) x hx hg

end GlobalTheory.CompanionTheory.ReesBasis
