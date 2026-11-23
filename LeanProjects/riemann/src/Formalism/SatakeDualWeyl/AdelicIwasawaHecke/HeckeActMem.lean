import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem out_smul (K : Subgroup G) (c : G) (x : G ⧸ K) :
    ∃ κ : K, (c • x).out = c * x.out * (κ : G) := by
  have h : ((c * x.out : G) : G ⧸ K) = ((c • x).out : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk]
    rfl
  refine ⟨⟨_, QuotientGroup.eq.1 h⟩, ?_⟩
  simp only [mul_inv_cancel_left]

theorem finsum_out_mul {M : Type} [AddCommMonoid M] (K : Subgroup G) (a : G) (F : G → M)
    (hF : ∀ (g : G) (c : K), F (g * c) = F g) :
    ∑ᶠ z : G ⧸ K, F (a * z.out) = ∑ᶠ y : G ⧸ K, F y.out := by
  have h : ∀ z : G ⧸ K, F (a * z.out) = F (a • z).out := by
    intro z
    obtain ⟨κ, hκ⟩ := out_smul K a z
    rw [hκ, hF]
  rw [finsum_congr h]
  exact finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun y => F y.out)

theorem finite_supp {k : Type} [CommRing k] (K : Subgroup G) (hK : IsCommensurated K)
    (f : G → k) (hf : f ∈ Hecke k K) : {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  obtain ⟨-, S, hS⟩ := hf'
  unfold IsCommensurated at hK
  have hfin : ∀ s : G, (Set.range fun k : K => ((↑k * s : G) : G ⧸ K)).Finite := by
    intro s
    let H : Subgroup K := (Subgroup.map (MulAut.conj s).toMonoidHom K).subgroupOf K
    haveI : H.FiniteIndex := ⟨hK s⟩
    haveI : Finite (K ⧸ H) := inferInstance
    let φ : K ⧸ H → G ⧸ K := Quotient.lift (fun k : K => ((↑k * s : G) : G ⧸ K)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
      have h2 : ((a⁻¹ * b : K) : G) ∈ Subgroup.map (MulAut.conj s).toMonoidHom K :=
        Subgroup.mem_subgroupOf.1 hab'
      obtain ⟨c, hc, hcab⟩ := Subgroup.mem_map.1 h2
      have e : (a : G)⁻¹ * b = s * c * s⁻¹ := by
        rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← hcab]
        rfl
      apply QuotientGroup.eq.2
      have : ((a : G) * s)⁻¹ * ((b : G) * s) = c := by
        calc ((a : G) * s)⁻¹ * ((b : G) * s) = s⁻¹ * ((a : G)⁻¹ * b) * s := by group
          _ = c := by rw [e]; group
      rw [this]
      exact hc)
    refine (Set.finite_range φ).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : K ⧸ H), rfl⟩
  refine (S.finite_toSet.biUnion fun s _ => hfin s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' x]
  apply QuotientGroup.eq.2
  rw [hab]
  have : ((a : G) * s)⁻¹ * ((a : G) * s * b) = b := by group
  rw [this]
  exact b.2

theorem amf_right {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    {Γ K : Subgroup G} {ρ : Representation k Γ W} {φ : G → W} (hφ : φ ∈ AMF k Γ K ρ)
    (g : G) (c : K) : φ (g * c) = φ g := by
  have h : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  simpa using h 1 g c

theorem hecke_act_mem : Formalism.UG.HeckeActMem := by
  intro G _ Γ K k _ W _ _ ρ hK f hf φ hφ
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  have hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g := hf'.1
  have hφ' : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  have hfin := finite_supp K hK f hf
  show ∀ (γ : Γ) (g : G) (κ : K), hAct K f φ (↑γ * g * ↑κ) = ρ γ (hAct K f φ g)
  intro γ g κ
  simp only [hAct]
  have step1 : ∀ x : G ⧸ K, f x.out • φ (↑γ * g * ↑κ * x.out) =
      ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) := by
    intro x
    obtain ⟨κ', hκ'⟩ := out_smul K (κ : G) x
    have h1 : x.out = (κ : G)⁻¹ * ((κ : G) • x).out * (κ' : G)⁻¹ := by rw [hκ']; group
    have e1 : f x.out = f ((κ : G) • x).out := by
      rw [h1]
      have := hbi κ⁻¹ κ'⁻¹ ((κ : G) • x).out
      simpa using this
    have e2 : φ (↑γ * g * ↑κ * x.out) = ρ γ (φ (g * ((κ : G) • x).out)) := by
      have : (↑γ : G) * g * ↑κ * x.out = ↑γ * (g * ((κ : G) • x).out) * ↑(κ'⁻¹) := by
        rw [h1, Subgroup.coe_inv]
        group
      rw [this, hφ']
    rw [e1, e2, map_smul]
  rw [finsum_congr step1]
  have hre : ∑ᶠ x : G ⧸ K, ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) =
      ∑ᶠ y : G ⧸ K, ρ γ (f y.out • φ (g * y.out)) :=
    finsum_comp_equiv (MulAction.toPerm (κ : G) : Equiv.Perm (G ⧸ K))
      (f := fun y => ρ γ (f y.out • φ (g * y.out)))
  rw [hre]
  have hsupp : (Function.support fun y : G ⧸ K => f y.out • φ (g * y.out)).Finite :=
    hfin.subset fun y hy => by
      intro h0
      exact hy (by simp [h0])
  exact (map_finsum (ρ γ) hsupp).symm

private theorem finite_support_left_translate_of_biinvariant {k : Type} [CommRing k] (K : Subgroup G) (f : G → k)
    (hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g) (hfin : {x : G ⧸ K | f x.out ≠ 0}.Finite)
    (a : G) : {x : G ⧸ K | f (a * x.out) ≠ 0}.Finite := by
  refine (hfin.preimage (f := fun x : G ⧸ K => a • x)
    fun _ _ _ _ h => MulAction.injective a h).subset ?_
  intro x hx
  show f (a • x).out ≠ 0
  obtain ⟨κ, hκ⟩ := out_smul K a x
  rw [hκ]
  have e : f (a * x.out * ↑κ) = f (a * x.out) := by simpa using hbi 1 κ (a * x.out)
  rw [e]
  exact hx

theorem hecke_act_mul : Formalism.UG.HeckeActMul := by
  intro G _ Γ K k _ W _ _ ρ hK f₁ hf₁ f₂ hf₂ φ hφ
  have hbi₂ : ∀ (a b : K) (g : G), f₂ (↑a * g * ↑b) = f₂ g :=
    (show IsBiInv K f₂ ∧ FinDosetSupp K f₂ from hf₂).1
  have hfin₁ := finite_supp K hK f₁ hf₁
  have hfin₂ := finite_supp K hK f₂ hf₂
  funext g
  simp only [hAct, conv]
  have hA : ∀ y : G ⧸ K, ∑ᶠ z : G ⧸ K, f₂ z.out • φ (g * y.out * z.out) =
      ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    intro y
    have := finsum_out_mul K y.out (fun h => f₂ (y.out⁻¹ * h) • φ (g * h)) (by
      intro h c
      show f₂ (y.out⁻¹ * (h * ↑c)) • φ (g * (h * ↑c)) = f₂ (y.out⁻¹ * h) • φ (g * h)
      rw [(by simp [mul_assoc] : y.out⁻¹ * (h * ↑c) = ↑(1 : K) * (y.out⁻¹ * h) * ↑c), hbi₂,
        (by rw [mul_assoc] : g * (h * ↑c) = g * h * ↑c), amf_right hφ])
    simpa [mul_assoc] using this
  simp_rw [hA]
  set A := hfin₁.toFinset with hAdef
  have hB : ∀ y : G ⧸ K, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}.Finite :=
    fun y => finite_support_left_translate_of_biinvariant K f₂ hbi₂ hfin₂ y.out⁻¹
  have hX : (⋃ y ∈ A, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}).Finite :=
    A.finite_toSet.biUnion fun y _ => hB y
  set X := hX.toFinset with hXdef
  have hAsub : ∀ y : G ⧸ K, f₁ y.out ≠ 0 → y ∈ A := fun y hy => hfin₁.mem_toFinset.2 hy
  have hXsub : ∀ y x : G ⧸ K, f₁ y.out ≠ 0 → f₂ (y.out⁻¹ * x.out) ≠ 0 → x ∈ X := by
    intro y x h1 h2
    rw [hX.mem_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 (hAsub y h1)) h2
  have hL : ∀ x : G ⧸ K, ∑ᶠ y : G ⧸ K, f₁ y.out * f₂ (y.out⁻¹ * x.out) =
      ∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out) := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro y hy
    exact hAsub y (left_ne_zero_of_mul hy)
  simp_rw [hL]
  have eL : ∑ᶠ x : G ⧸ K, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) =
      ∑ x ∈ X, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) := by
    apply finsum_eq_sum_of_support_subset
    intro x hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_smul hx)
    exact hXsub y x (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)
  have eR : ∑ᶠ y : G ⧸ K, f₁ y.out • ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) =
      ∑ y ∈ A, f₁ y.out • ∑ x ∈ X, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    rw [finsum_eq_sum_of_support_subset (s := A) _ (fun y hy => hAsub y (left_ne_zero_of_smul hy))]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [finsum_eq_sum_of_support_subset (s := X) _
      (fun x hx => hXsub y x (hfin₁.mem_toFinset.1 hy) (left_ne_zero_of_smul hx))]
  rw [eL, eR]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

end Formalism.UG.P
