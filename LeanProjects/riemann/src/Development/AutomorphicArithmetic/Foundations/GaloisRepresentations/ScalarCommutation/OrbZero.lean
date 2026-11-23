import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralSimpleAlgebraEmbeddingsConjugate

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix Polynomial GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {A B : Type} [Group A] [Group B]

theorem finsum_mul_eq_zero {ι : Type} (w : ℂ) (g : ι → ℂ) (h : ∑ᶠ i, g i = 0) :
    ∑ᶠ i, w * g i = 0 := by
  have := smul_finsum (R := ℂ) (M := ℂ) w g
  simp only [smul_eq_mul] at this
  rw [← this, h, mul_zero]

theorem map_conj_inf_of_comm (T L : Subgroup A) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {t : A} (ht : t ∈ T) :
    (T ⊓ L).map (MulAut.conj t).toMonoidHom = T ⊓ L := by
  have hfix : ∀ y ∈ T ⊓ L, (MulAut.conj t).toMonoidHom y = y := by
    intro y hy
    have hc := hT t ht y (Subgroup.mem_inf.mp hy).1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem oTerm_inv_of_comm (K C : Subgroup A) (δ : A) (f : A → ℂ)
    (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * MonoidHom.id A k) = f y)
    (hT : ∀ a ∈ twCent (MonoidHom.id A) δ, ∀ b ∈ twCent (MonoidHom.id A) δ, a * b = b * a)
    {t k : A} (ht : t ∈ twCent (MonoidHom.id A) δ) (hk : k ∈ K) (x : A) :
    oTerm (MonoidHom.id A) K C δ f (t * x * k) = oTerm (MonoidHom.id A) K C δ f x := by
  unfold oTerm
  rw [f_inv _ K δ f hf ht hk x, map_conj_mul_three_subgroup_of_mem K hk, inf_map_conj _ _ ht, map_conj_inf_of_comm _ _ hT ht]

theorem orbK_prod_eq_zero_of_slices (K₁ : Subgroup A) (K₂ : Subgroup B) (a : A) (b : B) (F : A × B → ℂ)
    (h₁ : ∀ s ∈ twCent (MonoidHom.id A) a, ∀ c ∈ twCent (MonoidHom.id A) a, s * c = c * s)
    (h₂ : ∀ s ∈ twCent (MonoidHom.id B) b, ∀ c ∈ twCent (MonoidHom.id B) b, s * c = c * s)
    (hF : ∀ k ∈ K₁.prod K₂, ∀ y, F (k⁻¹ * y * MonoidHom.id (A × B) k) = F y)
    (h0 : ∀ z : B, orbK (MonoidHom.id A) K₁ a (fun v => F (v, z)) = 0) :
    orbK (MonoidHom.id (A × B)) (K₁.prod K₂) (a, b) F = 0 := by
  have hTeq : twCent (MonoidHom.id (A × B)) (a, b) =
      (twCent (MonoidHom.id A) a).prod (twCent (MonoidHom.id B) b) := by
    ext g
    rw [Subgroup.mem_prod]
    show g * (a, b) = (a, b) * g ↔ g.1 * a = a * g.1 ∧ g.2 * b = b * g.2
    exact Prod.ext_iff
  have hcomm : ∀ s ∈ twCent (MonoidHom.id (A × B)) (a, b), ∀ c ∈ twCent (MonoidHom.id (A × B)) (a, b),
      s * c = c * s := by
    rw [hTeq]
    intro s hs c hc
    rw [Subgroup.mem_prod] at hs hc
    exact Prod.ext (h₁ _ hs.1 _ hc.1) (h₂ _ hs.2 _ hc.2)
  have hinv : ∀ x : A × B,
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F
        (DoubleCoset.mk (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) x).out =
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F x := by
    intro x
    obtain ⟨t, k, ht, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) x
    rw [he]
    exact oTerm_inv_of_comm _ _ _ F hF hcomm ht hk x
  have hsplit : ∀ (x : A) (y : B),
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F (x, y) =
      ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj y).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a (fun v => F (v, y⁻¹ * b * y)) x := by
    intro x y
    unfold oTerm
    rw [hTeq, map_conj_prod, prod_inf_prod, prod_inf_prod, vol_prod]
    simp only [Rat.cast_mul, mul_inv, MonoidHom.id_apply, Prod.inv_mk, Prod.mk_mul_mk]
    ring
  have hbij : Function.Bijective (fun z : DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁ ×
      DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂ =>
        DoubleCoset.mk (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) (z.1.out, z.2.out)) := by
    rw [hTeq]
    exact dcPair_bij _ _ _ _
  unfold orbK
  rw [orbC_eq, ← finsum_comp_equiv (Equiv.ofBijective _ hbij)]
  simp only [Equiv.ofBijective_apply, hinv, hsplit]
  rw [← finsum_comp_equiv (Equiv.prodComm _ _)]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  have hin : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂,
      ∑ᶠ p : DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁,
        ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj q.out).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a
          (fun v => F (v, q.out⁻¹ * b * q.out)) p.out = 0 := by
    intro q
    apply finsum_mul_eq_zero
    have := h0 (q.out⁻¹ * b * q.out)
    unfold orbK at this
    rwa [orbC_eq] at this
  rcases Set.finite_or_infinite (Function.support fun z :
      DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂ ×
        DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁ =>
      ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj z.1.out).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a
          (fun v => F (v, z.1.out⁻¹ * b * z.1.out)) z.2.out) with hfin | hinf
  · rw [finsum_curry _ hfin]
    simp only [hin, finsum_zero]
  · exact finsum_of_infinite_support hinf

end Abstract

section Topology

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem isLocallyConstant_of_right_inv (K₀ : Subgroup Γ) (ho : IsOpen (K₀ : Set Γ)) (f : Γ → ℂ)
    (hf : ∀ g, ∀ c ∈ K₀, f (g * c) = f g) : IsLocallyConstant f := by
  refine fun s => ?_
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (K₀ : Set Γ), ?_, ho.preimage (by fun_prop), ?_⟩
  · intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hy ⊢
    have := hf x (x⁻¹ * y) hy
    rw [mul_inv_cancel_left] at this
    rw [this]
    exact hx
  · simp [K₀.one_mem]

theorem hasCompactSupport_of_doubleCosets (K₀ : Subgroup Γ) (hc : IsCompact (K₀ : Set Γ)) (f : Γ → ℂ) (S : Finset Γ)
    (hf : ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ a ∈ K₀, ∃ b ∈ K₀, g = a * s * b) : HasCompactSupport f := by
  let U : Set Γ := ⋃ s ∈ S, (fun q : Γ × Γ => q.1 * s * q.2) '' ((K₀ : Set Γ) ×ˢ (K₀ : Set Γ))
  have hU : IsCompact U := by
    refine S.isCompact_biUnion fun s _ => ?_
    exact (hc.prod hc).image (by fun_prop)
  have hsub : Function.support f ⊆ U := by
    intro g hg
    obtain ⟨s, hs, a, ha, b, hb, rfl⟩ := hf g hg
    exact Set.mem_biUnion hs ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  exact IsCompact.of_isClosed_subset hU.closure isClosed_closure (closure_mono hsub)

end Topology

section Split

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem orbK_eq_zero_of_cuspSlices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] [Algebra G.F k] {P : Pl G k}
    {K : Subgroup G.GAf} {H : Type} [Group H] [TopologicalSpace H] (S : Split P K H) (f : G.GAf → ℂ)
    (hf : f ∈ Hecke ℂ K) (hC : S.Cusp f) (γ : G.GAf) (hs : (P.at γ).charpoly.Separable)
    (hi : ¬ Irreducible (P.at γ).charpoly)
    (hcomm : ∀ a ∈ twCent (MonoidHom.id G.GAf) γ, ∀ b ∈ twCent (MonoidHom.id G.GAf) γ, a * b = b * a) :
    orbK (MonoidHom.id G.GAf) K γ f = 0 := by
  have : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  obtain ⟨hbi, hfin⟩ := hf
  set F : GL (Fin G.n) k × H → ℂ := fun z => f (S.e.symm z) with hFdef
  have hFbi : ∀ k₁ ∈ S.K₀.prod S.K', ∀ k₂ ∈ S.K₀.prod S.K', ∀ y, F (k₁ * y * k₂) = F y := by
    intro k₁ hk₁ k₂ hk₂ y
    rw [← S.map_eq] at hk₁ hk₂
    obtain ⟨a, ha, rfl⟩ := hk₁
    obtain ⟨b, hb, rfl⟩ := hk₂
    simp only [hFdef, MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply]
    exact hbi ⟨a, ha⟩ ⟨b, hb⟩ _
  have hcommB : ∀ s ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ),
      ∀ c ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ), s * c = c * s := by
    intro s hs c hc
    rw [← GlobalTheory.VanishNonEll.map_twCent_id] at hs hc
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm s' hs' c' hc']
  have hF' : ∀ q ∈ Subgroup.map S.e.toMonoidHom K, ∀ y,
      F (q⁻¹ * y * MonoidHom.id (GL (Fin G.n) k × H) q) = F y := by
    rw [S.map_eq]
    intro q hq y
    exact hFbi q⁻¹ ((S.K₀.prod S.K').inv_mem hq) q hq y
  rw [GlobalTheory.VanishNonEll.orbK_congr_equiv S.e K γ f
    (fun t ht q hq x => oTerm_inv_of_comm _ _ _ F hF' hcommB ht hq x)]
  rw [S.map_eq]
  have hsep : (((S.e γ).1 : GL (Fin G.n) k) : Matrix (Fin G.n) (Fin G.n) k).charpoly.Separable := by
    rw [S.e_at]
    exact hs
  have hirr : ¬ Irreducible (((S.e γ).1 : GL (Fin G.n) k) : Matrix (Fin G.n) (Fin G.n) k).charpoly := by
    rw [S.e_at]
    exact hi
  have h₁ : ∀ s ∈ twCent (MonoidHom.id (GL (Fin G.n) k)) (S.e γ).1,
      ∀ c ∈ twCent (MonoidHom.id (GL (Fin G.n) k)) (S.e γ).1, s * c = c * s :=
    fun s hs c hc => GlobalTheory.CentSep.centraliser_comm_of_separable k (Fin G.n) (S.e γ).1 s c hsep hs hc
  have hmem2 : ∀ s ∈ twCent (MonoidHom.id H) (S.e γ).2,
      ((1 : GL (Fin G.n) k), s) ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ) := by
    intro s hs
    show ((1 : GL (Fin G.n) k), s) * S.e γ = S.e γ * ((1 : GL (Fin G.n) k), s)
    refine Prod.ext ?_ hs
    simp
  have h₂ : ∀ s ∈ twCent (MonoidHom.id H) (S.e γ).2,
      ∀ c ∈ twCent (MonoidHom.id H) (S.e γ).2, s * c = c * s := by
    intro s hs c hc
    have := congrArg Prod.snd (hcommB _ (hmem2 s hs) _ (hmem2 c hc))
    simpa using this
  have h0 : ∀ z : H, orbK (MonoidHom.id (GL (Fin G.n) k)) S.K₀ (S.e γ).1 (fun v => F (v, z)) = 0 := by
    intro z
    have hbi0 : ∀ a ∈ S.K₀, ∀ b ∈ S.K₀, ∀ g, F (a * g * b, z) = F (g, z) := by
      intro a ha b hb g
      have := hFbi (a, 1) ⟨ha, S.K'.one_mem⟩ (b, 1) ⟨hb, S.K'.one_mem⟩ (g, z)
      simpa using this
    have hlc : IsLocallyConstant (fun v => F (v, z)) :=
      isLocallyConstant_of_right_inv S.K₀ S.open₀ _ (fun g c hc => by
        have := hbi0 1 S.K₀.one_mem c hc g
        simpa using this)
    have hcs : HasCompactSupport (fun v => F (v, z)) := by
      obtain ⟨T, hT⟩ := hfin
      refine hasCompactSupport_of_doubleCosets S.K₀ S.cpt₀ _ (T.image fun s => (S.e s).1) ?_
      intro v hv
      obtain ⟨s, hsT, a, b, hab⟩ := hT (S.e.symm (v, z)) hv
      have ha : S.e a ∈ S.K₀.prod S.K' := by
        rw [← S.map_eq]
        exact ⟨a, a.2, rfl⟩
      have hb : S.e b ∈ S.K₀.prod S.K' := by
        rw [← S.map_eq]
        exact ⟨b, b.2, rfl⟩
      have hv' : (v, z) = S.e a * S.e s * S.e b := by
        rw [← map_mul, ← map_mul, ← hab, MulEquiv.apply_symm_apply]
      refine ⟨(S.e s).1, Finset.mem_image_of_mem _ hsT, (S.e a).1, ha.1, (S.e b).1, hb.1, ?_⟩
      have := congrArg Prod.fst hv'
      simpa using this
    exact orbK_eq_zero_of_cusp k (Fin G.n) (fun v => F (v, z)) hlc hcs (hC z) (S.e γ).1 hsep hirr
      S.K₀ S.open₀ S.cpt₀ hbi0
  exact orbK_prod_eq_zero_of_slices S.K₀ S.K' (S.e γ).1 (S.e γ).2 F h₁ h₂ (fun q hq y => hFbi q⁻¹
    ((S.K₀.prod S.K').inv_mem hq) q hq y) h0

end Split

end UpperTheory.Gal.Spc
