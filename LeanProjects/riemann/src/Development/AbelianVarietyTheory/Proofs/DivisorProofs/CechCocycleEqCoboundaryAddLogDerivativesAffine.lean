import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleEqTopOfSupMaximalSmulEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesModStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechH1Span

theorem resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

set_option maxHeartbeats 1000000 in

theorem exists_dlog_add_coboundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj c hc
  let ρ : ∀ p : J × J, Γ(X, U.1) →+* Γ(t.G.left, W p.1 ⊓ W p.2) := fun p =>
    (t.G.hom.appLE U.1 (W p.1 ⊓ W p.2) (inf_le_left.trans (hWU p.1))).hom
  letI inst : ∀ p : J × J, Module Γ(X, U.1) Γ(t.G.left, W p.1 ⊓ W p.2) := fun p => Module.compHom _ (ρ p)
  have smul_apply : ∀ (r : Γ(X, U.1)) (x : ∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) (p : J × J),
      (r • x) p = ρ p r * x p := fun _ _ _ => rfl
  let Z : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (x (i, i')) +
          resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
            (x (i', i'')) =
          resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
            (x (i, i''))}
      add_mem' := by
        intro a b ha hb i i' i''
        simp only [Pi.add_apply, map_add]
        rw [← ha i i' i'', ← hb i i' i'']
        abel
      zero_mem' := by
        intro i i' i''
        simp
      smul_mem' := by
        intro r x hx i i' i''
        simp only [smul_apply, map_mul]
        rw [← hx i i' i'']
        simp only [ρ, resG_appLE]
        ring }
  let Bd : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∃ h : ∀ i : J, Γ(t.G.left, W i), ∀ i i',
          x (i, i') = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i')}
      add_mem' := by
        rintro a b ⟨h1, e1⟩ ⟨h2, e2⟩
        refine ⟨h1 + h2, fun i i' => ?_⟩
        simp only [Pi.add_apply, map_add, e1, e2]
        ring
      zero_mem' := ⟨0, fun i i' => by simp⟩
      smul_mem' := by
        rintro r x ⟨h1, e1⟩
        refine ⟨fun i => (t.G.hom.appLE U.1 (W i) (hWU i)).hom r * h1 i, fun i i' => ?_⟩
        simp only [smul_apply, e1, map_mul, resG_appLE, ρ]
        ring }
  let κ : Fin n → (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) := fun b p =>
    δ b (W p.1 ⊓ W p.2) (resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2)).val) *
      resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2))⁻¹.val
  let S : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    Bd ⊔ Submodule.span Γ(X, U.1) (Set.range κ)
  let S' : Submodule Γ(X, U.1) Z := S.comap Z.subtype
  obtain ⟨N, e, he, hAe⟩ := GlobalTheory.T.cech_h1_finite_generation_affine E H X t hP hA U J W hWa hcov hWU
  let ek : Fin N → Z := fun k => ⟨fun p => e k p.1 p.2, he k⟩
  have hspan : Submodule.span Γ(X, U.1) (Set.range fun k => S'.mkQ (ek k)) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨r, h, hz⟩ := hAe (fun i i' => z.1 (i, i')) (z.2)
    have hmem : z - ∑ k, r k • ek k ∈ S' := by
      refine Submodule.mem_sup_left ⟨h, fun i i' => ?_⟩
      change z.1 (i, i') - (∑ k, r k • ek k).1 (i, i') = _
      rw [Submodule.coe_sum, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ]
      exact add_sub_cancel_right _ _
    have : S'.mkQ z = ∑ k, r k • S'.mkQ (ek k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite Γ(X, U.1) (Z ⧸ S') := ⟨⟨Finset.univ.image fun k => S'.mkQ (ek k), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan⟩⟩
  have hbot := GlobalTheory.submodule_eq_top_of_sup_maximal_smul_eq_top Γ(X, U.1) (Z ⧸ S') ⊥ (fun m hm => by
    rw [bot_sup_eq]
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨θ, h, N', r, e', hr, he', hz⟩ :=
      GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_mod E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
        (fun i i' => z.1 (i, i')) z.2
    let ek' : Fin N' → Z := fun k => ⟨fun p => e' k p.1 p.2, he' k⟩
    have hmem : z - ∑ k, r k • ek' k ∈ S' := by
      have hw : ∑ b, θ b • κ b ∈ Submodule.span Γ(X, U.1) (Set.range κ) :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
      have hy : (fun p : J × J => resG t.G.left (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1) (h p.1) -
          resG t.G.left (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2) (h p.2)) ∈ Bd := ⟨h, fun i i' => rfl⟩
      change (z - ∑ k, r k • ek' k : Z).1 ∈ S
      refine Submodule.mem_sup.2 ⟨_, hy, _, hw, ?_⟩
      funext p
      obtain ⟨i, i'⟩ := p
      change _ = z.1 (i, i') - (∑ k, r k • ek' k).1 (i, i')
      rw [Submodule.coe_sum, Finset.sum_apply, Pi.add_apply, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ, κ]
      exact (add_sub_cancel_right _ _).symm
    have hq : S'.mkQ z = ∑ k, r k • S'.mkQ (ek' k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek' k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [hq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hr k) Submodule.mem_top)
  let cz : Z := ⟨fun p => c p.1 p.2, hc⟩
  have hcz : S'.mkQ cz = 0 := by
    have : S'.mkQ cz ∈ (⊥ : Submodule Γ(X, U.1) (Z ⧸ S')) := hbot ▸ Submodule.mem_top
    exact (Submodule.mem_bot _).1 this
  have hcS0 : cz ∈ S' := (Submodule.Quotient.mk_eq_zero S').1 hcz
  have hcS : cz.1 ∈ S := hcS0
  obtain ⟨y, ⟨h, hy⟩, w, hw, hyw⟩ := Submodule.mem_sup.1 hcS
  obtain ⟨θ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
  refine ⟨θ, h, fun i i' => ?_⟩
  have k := congrFun hyw (i, i')
  change _ = c i i' at k
  rw [← k, Pi.add_apply, hy i i', Finset.sum_apply]
  simp only [smul_apply, ρ, κ]

end GlobalTheory.CechH1Span
