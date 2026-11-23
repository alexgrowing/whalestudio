import Development.DiscreteGroups.GlobalIrreducibility.LConvAltB

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem altIdentity : AltIdentity := by
  intro G _ _ _ K hKo hKc _ N hN H _ _ _ π hπ e he hKe hfix d hd g
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hd
    exact Nat.not_lt_zero _ hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd0
  have hstar : ∀ a, star (π a) = π a⁻¹ := alt_star_eq π hπ
  have hes : star e = e := he.star_eq
  have hKe' : ∀ κ ∈ K, π κ * e = e := fun κ hκ => ContinuousLinearMap.ext fun x => hKe x κ hκ
  have hee : e * e = e := ContinuousLinearMap.ext fun x => hfix (e x) fun κ hκ => hKe x κ hκ
  have heK : ∀ κ ∈ K, e * π κ = e := by
    intro κ hκ
    have h1 := hKe' κ⁻¹ (K.inv_mem hκ)
    calc e * π κ = star (π κ⁻¹ * e) := by rw [star_mul, hes, hstar, inv_inv]
      _ = e := by rw [h1, hes]
  let f : G → (H →L[ℂ] H) := fun a => e * π a * e
  let Y : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ (Set.range fun a => π a * e)
  have hY1 : ∀ a, ∀ y ∈ Y, π a * y ∈ Y := by
    intro a y hy
    have : Y ≤ Y.comap (LinearMap.mulLeft ℂ (π a)) := Submodule.span_le.mpr (by
      rintro _ ⟨b, rfl⟩
      show π a * (π b * e) ∈ Y
      exact Submodule.subset_span ⟨a * b, by simp only [map_mul, mul_assoc]⟩)
    exact this hy
  have hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨K.comap (MulAut.conj a⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
      · have : ((K.comap (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun h => a⁻¹ * h * a) ⁻¹' (K : Set G) := by
          ext h; simp
        rw [this]
        exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · have hu' : a⁻¹ * u * a ∈ K := by simpa [MulAut.conj_apply] using hu
        calc π u * (π a * e) = π (u * a) * e := by rw [map_mul, mul_assoc]
          _ = π (a * (a⁻¹ * u * a)) * e := by rw [show a * (a⁻¹ * u * a) = u * a by group]
          _ = π a * (π (a⁻¹ * u * a) * e) := by rw [map_mul, mul_assoc]
          _ = π a * e := by rw [hKe' _ hu']
    | zero => exact ⟨⊤, by simp, fun u _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨U₁, h1o, h1⟩ := hx
      obtain ⟨U₂, h2o, h2⟩ := hz
      refine ⟨U₁ ⊓ U₂, by rw [Subgroup.coe_inf]; exact h1o.inter h2o, fun u hu => ?_⟩
      rw [mul_add, h1 u hu.1, h2 u hu.2]
    | smul c x _ hx =>
      obtain ⟨U, ho, h⟩ := hx
      exact ⟨U, ho, fun u hu => by rw [mul_smul_comm, h u hu]⟩
  have hYe : ∀ y ∈ Y, y * e = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; simp only [mul_assoc, hee]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul, hx, hz]
    | smul c x _ hx => rw [smul_mul_assoc, hx]
  have heY : e ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hE : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) → ∀ z ∈ Z, e * z ∈ Z := by
    intro Z hZY hZ z hz
    obtain ⟨U, hUo, hU⟩ := hSm z (hZY hz)
    exact alt_avg K hKc π e heK hfix Z (fun κ _ => hZ κ) z hz U hUo hU
  have hYE : ∀ y ∈ Y, e * y ∈ Y := hE Y le_rfl hY1
  have hYmul : ∀ x ∈ Y, ∀ y ∈ Y, x * y ∈ Y := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      show π a * e * y ∈ Y
      rw [mul_assoc]; exact hY1 a _ (hYE y hy)
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact Y.add_mem hx hz
    | smul c x _ hx => rw [smul_mul_assoc]; exact Y.smul_mem c hx
  have hword : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ l : List G, ∀ z ∈ Z, (l.map f).prod * z ∈ Z := by
    intro Z hZY hZ l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons a l ih =>
      intro z hz
      rw [List.map_cons, List.prod_cons, mul_assoc]
      show e * π a * e * ((l.map f).prod * z) ∈ Z
      rw [mul_assoc, mul_assoc]
      exact hE Z hZY hZ _ (hZ a _ (hE Z hZY hZ _ (ih z hz)))
  have hfstar : ∀ a, star (f a) = f a⁻¹ := by
    intro a
    show star (e * π a * e) = e * π a⁻¹ * e
    simp only [star_mul, hes, hstar, mul_assoc]
  have hwstar : ∀ l : List G, star ((l.map f).prod) = ((l.reverse.map (·⁻¹)).map f).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, ih, hfstar]
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f := by
    intro σ; rw [List.map_ofFn]; rfl
  set S := ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun i => e * π (g (σ i)) * e).prod with hSdef
  have hSZ : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ z ∈ Z, S * z ∈ Z ∧ star S * z ∈ Z := by
    intro Z hZY hZ z hz
    constructor
    · rw [hSdef, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [smul_mul_assoc, hterm]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
    · rw [hSdef, star_sum, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [star_smul, star_intCast, hterm, hwstar, smul_mul_assoc]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
  have hQ : ∀ (l : List G) a, f a * (l.map f).prod * e = f a * (l.map f).prod := by
    intro l
    induction l with
    | nil =>
      intro a
      simp only [List.map_nil, List.prod_nil, mul_one]
      show e * π a * e * e = e * π a * e
      rw [mul_assoc, hee]
    | cons b l ih => intro a; rw [List.map_cons, List.prod_cons, mul_assoc (f a), ih b]
  have hSe : S * e = S := by
    rw [hSdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, hterm, List.ofFn_succ, List.map_cons, List.prod_cons, hQ]
  have heSs : e * star S = star S := by
    have := congrArg star hSe
    rwa [star_mul, hes] at this
  have hSY : S ∈ Y := by rw [← hSe]; exact (hSZ Y le_rfl hY1 e heY).1
  by_contra hS
  have : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne S 0 hS
  set c := star S * S with hc
  have hcsa : IsSelfAdjoint c := IsSelfAdjoint.star_mul_self S
  have hc0 : c ≠ 0 := by
    intro h0
    have : ‖S‖ * ‖S‖ = 0 := by rw [← CStarRing.norm_star_mul_self, ← hc, h0, norm_zero]
    exact hS (norm_eq_zero.mp (mul_self_eq_zero.mp this))
  have hec : e * c = c := by rw [hc, ← mul_assoc, heSs]
  have hcY : c ∈ Y := (hSZ Y le_rfl hY1 S hSY).2
  obtain ⟨z, hz, hzn⟩ := spectrum.exists_nnnorm_eq_spectralRadius c
  rw [hcsa.spectralRadius_eq_nnnorm] at hzn
  have hz0 : z ≠ 0 := by
    intro h0
    apply hc0
    rw [h0, nnnorm_zero, ENNReal.coe_zero, eq_comm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hzn
    exact hzn
  have hzr : star z = z := by
    rw [hcsa.mem_spectrum_eq_re hz]
    exact Complex.conj_ofReal _
  have hnotl : ∀ y ∈ Y, y * (c - z • e) ≠ e := by
    intro y hy hyu
    set b := e * y with hb
    have hbe : b * e = b := by rw [hb, mul_assoc, hYe y hy]
    have hbu : b * (c - z • e) = e := by rw [hb, mul_assoc, hyu, hee]
    have h1 : b * (c - z • (1 : H →L[ℂ] H)) = e := by
      calc b * (c - z • (1 : H →L[ℂ] H)) = b * c - z • b := by rw [mul_sub, mul_smul_comm, mul_one]
        _ = b * c - z • (b * e) := by rw [hbe]
        _ = b * (c - z • e) := by rw [mul_sub, mul_smul_comm]
        _ = e := hbu
    have h2 : (1 - e) * (c - z • (1 : H →L[ℂ] H)) = -(z • (1 - e)) := by
      rw [sub_mul, one_mul, mul_sub, hec, mul_smul_comm, mul_one, smul_sub]
      abel
    have hL : (b - z⁻¹ • (1 - e)) * (c - z • (1 : H →L[ℂ] H)) = 1 := by
      rw [sub_mul, h1, smul_mul_assoc, h2, smul_neg, smul_smul, inv_mul_cancel₀ hz0, one_smul]
      abel
    set L := b - z⁻¹ • (1 - e) with hLd
    have hv : star (c - z • (1 : H →L[ℂ] H)) = c - z • 1 := by
      rw [star_sub, hcsa.star_eq, star_smul, hzr, star_one]
    have hR : (c - z • (1 : H →L[ℂ] H)) * star L = 1 := by
      have := congrArg star hL
      rwa [star_mul, hv, star_one] at this
    have hLR : L = star L := by
      calc L = L * ((c - z • (1 : H →L[ℂ] H)) * star L) := by rw [hR, mul_one]
        _ = star L := by rw [← mul_assoc, hL, one_mul]
    have hunit : IsUnit (c - z • (1 : H →L[ℂ] H)) := ⟨⟨c - z • 1, L, by rw [hLR]; exact hR, hL⟩, rfl⟩
    apply spectrum.mem_iff.mp hz
    rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
    exact hunit.neg
  let s : Set (Submodule ℂ (H →L[ℂ] H)) := {Z | Z ≤ Y ∧ (∀ a, ∀ x ∈ Z, π a * x ∈ Z) ∧ e ∉ Z}
  have hZ0 : Y.map (LinearMap.mulRight ℂ (c - z • e)) ∈ s := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      show y * (c - z • e) ∈ Y
      rw [mul_sub, mul_smul_comm, hYe y hy]
      exact Y.sub_mem (hYmul y hy c hcY) (Y.smul_mem z hy)
    · rintro a _ ⟨y, hy, rfl⟩
      exact ⟨π a * y, hY1 a y hy, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, hyu⟩
      exact hnotl y hy hyu
  obtain ⟨Y', hZY', hmax⟩ := zorn_le_nonempty₀ s (by
    intro C hCs hC Z0 hZ0C
    refine ⟨sSup C, ⟨sSup_le fun Z hZ => (hCs hZ).1, ?_, ?_⟩, fun Z hZ => le_sSup hZ⟩
    · intro a x hx
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp hx
      exact le_sSup hZ ((hCs hZ).2.1 a x hxZ)
    · intro he'
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp he'
      exact (hCs hZ).2.2 hxZ) _ hZ0
  obtain ⟨hY'Y, hY'G, heY'⟩ := hmax.prop
  have hY'E : ∀ x ∈ Y', e * x ∈ Y' := hE Y' hY'Y hY'G
  have hq := alt_quot K N hN π e hKe' hee Y Y' le_rfl heY hY1 hYE hSm hY'Y hY'G hY'E heY'
    (fun Z hZY hZG heZ hle => hmax.le_of_ge ⟨hZY, hZG, heZ⟩ hle) (n + 1) hd g
  rw [← hSdef, hSe] at hq
  have hcY' : c ∈ Y' := (hSZ Y' hY'Y hY'G S hq).2
  have huY' : c - z • e ∈ Y' := by
    have h := hZY' ⟨e, heY, rfl⟩
    have h' : (LinearMap.mulRight ℂ (c - z • e)) e = c - z • e := by
      rw [LinearMap.mulRight_apply, mul_sub, hec, mul_smul_comm, hee]
    rwa [h'] at h
  have hze : z • e ∈ Y' := by
    have := Y'.sub_mem hcY' huY'
    rwa [sub_sub_cancel] at this
  apply heY'
  have := Y'.smul_mem z⁻¹ hze
  rwa [smul_smul, inv_mul_cancel₀ hz0, one_smul] at this

end DiscreteGroups.sglob.LConv
