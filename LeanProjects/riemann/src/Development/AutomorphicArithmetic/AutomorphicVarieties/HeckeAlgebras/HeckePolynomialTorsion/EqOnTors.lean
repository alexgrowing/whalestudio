import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.JEx

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)

theorem art_ine {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (σ : Ine (F := F) A) :
    a (ineIncl h σ) ∈ Uo (w.adicCompletion F) :=
  ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero])

theorem char_triv {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) {B : Type} [Group B]
    (χ : Dec (F := F) A →* B) (hχ : IsLocallyConstant χ) (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 1)
    (s : Weil h) (hs : a s = unif _) (h1 : χ (Subgroup.inclusion (Weil_le_Dec h) s) = 1) : χ = 1 := by
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have hdeg : deg s⁻¹ = 1 := by
    rw [deg_inv, ← ha.ord_eq, hs]
    exact ord_eq_one GlAx.unif_spec
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have := hd.equalizer hχ.continuous (continuous_const (y := (1 : B))) (funext fun t => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hdeg t
    change χ (Subgroup.inclusion (Weil_le_Dec h) t) = 1
    rw [hτ, map_mul, map_mul, map_zpow, map_zpow, map_inv, map_inv, h1, inv_one, one_zpow, one_mul]
    exact hI _ τ.2)
  exact MonoidHom.ext fun g => congrFun this g

private theorem ext_lc {D W B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W] [Group B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (V : Subgroup D) [V.Normal] (hV : IsOpen (V : Set D))
    (hχ : ∀ s, i s ∈ V → χ s = 1) : ∃ ψ : D →* B, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = χ s := by
  have hex : ∀ d : D, ∃ s : W, d⁻¹ * i s ∈ V := by
    intro d
    have ho : IsOpen {x : D | d⁻¹ * x ∈ V} := hV.preimage (continuous_const.mul continuous_id)
    have hn : ({x : D | d⁻¹ * x ∈ V} : Set D).Nonempty := ⟨d, by simp [V.one_mem]⟩
    exact hi.exists_mem_open ho hn
  have key : ∀ (d : D) (s s' : W), d⁻¹ * i s ∈ V → d⁻¹ * i s' ∈ V → χ s = χ s' := by
    intro d s s' h1 h2
    have h3 : i (s⁻¹ * s') ∈ V := by
      have : i (s⁻¹ * s') = (d⁻¹ * i s)⁻¹ * (d⁻¹ * i s') := by
        rw [map_mul, map_inv]
        group
      rw [this]
      exact V.mul_mem (V.inv_mem h1) h2
    have h4 := hχ _ h3
    rw [map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4
  choose f hf using hex
  refine ⟨{ toFun := fun d => χ (f d), map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · show χ (f 1) = 1
    rw [← χ.map_one]
    exact key 1 _ _ (hf 1) (by simp [V.one_mem])
  · intro d1 d2
    show χ (f (d1 * d2)) = χ (f d1) * χ (f d2)
    rw [← map_mul]
    apply key (d1 * d2) _ _ (hf _)
    have e : (d1 * d2)⁻¹ * i (f d1 * f d2) = (d2⁻¹ * (d1⁻¹ * i (f d1)) * d2⁻¹⁻¹) * (d2⁻¹ * i (f d2)) := by
      rw [map_mul]
      group
    rw [e]
    exact V.mul_mem (‹V.Normal›.conj_mem _ (hf d1) _) (hf d2)
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y : D | x⁻¹ * y ∈ V}, hV.preimage (continuous_const.mul continuous_id), by simp [V.one_mem], ?_⟩
    intro y hy
    show χ (f y) = χ (f x)
    symm
    apply key x _ _ (hf x)
    have e : x⁻¹ * i (f y) = (x⁻¹ * y) * (y⁻¹ * i (f y)) := by group
    rw [e]
    exact V.mul_mem hy (hf y)
  · intro s
    show χ (f (i s)) = χ s
    exact key (i s) _ _ (hf _) (by simp [V.one_mem])

private theorem locallyConstant_hom_trivial_on_commutator_closure {D W C : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W]
    [Group C] (i : W →* D) (hi : DenseRange i) (P : D →* C) (hP : IsLocallyConstant P)
    (hc : ∀ s t, P (i s) * P (i t) = P (i t) * P (i s)) (x : D)
    (hx : x ∈ (commutator D).topologicalClosure) : P x = 1 := by
  have hlift : ∀ y : D, ∃ s, P (i s) = P y := by
    intro y
    obtain ⟨s, hs⟩ := hi.exists_mem_open (hP.isOpen_fiber (P y)) ⟨y, rfl⟩
    exact ⟨s, hs⟩
  have hcomm : ∀ y z : D, P y * P z = P z * P y := by
    intro y z
    obtain ⟨s, hs⟩ := hlift y
    obtain ⟨t, ht⟩ := hlift z
    rw [← hs, ← ht]
    exact hc s t
  have hle : commutator D ≤ P.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro g1 _ g2 _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm g1 g2
  exact Subgroup.topologicalClosure_minimal _ hle (hP.isClosed_fiber 1) hx

include h in

theorem char_tors {B : Type} [Group B] [Finite B] (χ : Dec (F := F) A →* B) (hχ : IsLocallyConstant χ)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 1) (g : Dec (F := F) A) (M : ℕ) (hM : 0 < M)
    (hg : g ^ M ∈ (commutator (Dec (F := F) A)).topologicalClosure) : χ g = 1 := by
  obtain ⟨φ0, hφ0⟩ : ∃ φ : Weil h, deg φ = 1 := ⟨frob h, deg_frob⟩
  have hnpos : 0 < Nat.card B := Nat.card_pos
  have hkpos : 0 < M * Nat.card B := Nat.mul_pos hM hnpos
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree F Ω A w h (M * Nat.card B) hkpos
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {ζ})) (Subgroup.one_mem _)
  let Hs : Subgroup (G F Ω) := (H.toOpenSubgroup : Subgroup (G F Ω))
  haveI hHn : Hs.Normal := H.isNormal'
  have hHo : IsOpen (Hs : Set (G F Ω)) := H.toOpenSubgroup.isOpen
  have hHfix : ∀ x : G F Ω, x ∈ Hs → x ζ = ζ := by
    intro x hx
    exact ((IntermediateField.mem_fixingSubgroup_iff _ x).mp (hH hx)) ζ
      (IntermediateField.mem_adjoin_simple_self F ζ)
  let V : Subgroup (Dec (F := F) A) := Hs.subgroupOf (Dec (F := F) A)
  haveI : V.Normal := hHn.subgroupOf _
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := hHo.preimage continuous_subtype_val
  have hi : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := weil_group_dense_in_galois_group F Ω w A h
  let χd : Weil h →* Multiplicative (ZMod (M * Nat.card B)) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (M * Nat.card B)))).comp (degHom h)
  have hχd : ∀ s, χd s = Multiplicative.ofAdd ((deg s : ℤ) : ZMod (M * Nat.card B)) := by
    intro s
    show Multiplicative.ofAdd (Int.castAddHom (ZMod (M * Nat.card B)) (Multiplicative.toAdd (degHom h s))) = _
    rw [degHom_apply]
    rfl
  obtain ⟨ψ, hψlc, hψ⟩ := ext_lc (Subgroup.inclusion (Weil_le_Dec h)) hi χd V hVo (by
    intro s hs
    rw [hχd, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hζ s (hHfix _ (Subgroup.mem_subgroupOf.mp hs)))
  have hχW : ∀ s : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) =
      χ (Subgroup.inclusion (Weil_le_Dec h) φ0) ^ deg s := by
    intro s
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ0 s
    conv_lhs => rw [hτ]
    rw [map_mul, map_mul, map_zpow, map_zpow, hI (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h τ)) τ.2, mul_one]
  have hc1 : ∀ s t : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) * χ (Subgroup.inclusion (Weil_le_Dec h) t) =
      χ (Subgroup.inclusion (Weil_le_Dec h) t) * χ (Subgroup.inclusion (Weil_le_Dec h) s) := by
    intro s t
    rw [hχW s, hχW t]
    exact ((Commute.refl _).zpow_zpow _ _).eq
  have hc2 : ∀ s t : Weil h, ψ (Subgroup.inclusion (Weil_le_Dec h) s) * ψ (Subgroup.inclusion (Weil_le_Dec h) t) =
      ψ (Subgroup.inclusion (Weil_le_Dec h) t) * ψ (Subgroup.inclusion (Weil_le_Dec h) s) :=
    fun s t => mul_comm _ _
  have h1 := locallyConstant_hom_trivial_on_commutator_closure _ hi χ hχ hc1 _ hg
  have h2 := locallyConstant_hom_trivial_on_commutator_closure _ hi ψ hψlc hc2 _ hg
  obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) σ) = χ g ∧
      ψ (Subgroup.inclusion (Weil_le_Dec h) σ) = ψ g := by
    obtain ⟨σ, hσ⟩ := hi.exists_mem_open ((hχ.isOpen_fiber (χ g)).inter (hψlc.isOpen_fiber (ψ g)))
      ⟨g, rfl, rfl⟩
    exact ⟨σ, hσ.1, hσ.2⟩
  rw [map_pow, ← hσ2, hψ, hχd, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
  have h3 : (((M * deg σ : ℤ)) : ZMod (M * Nat.card B)) = 0 := by
    push_cast
    exact h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have h4 : (Nat.card B : ℤ) ∣ deg σ := by
    push_cast at h3
    exact (mul_dvd_mul_iff_left hM0).mp h3
  obtain ⟨m, hm⟩ := h4
  rw [← hσ1, hχW, hm, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow]

include h in

theorem eq_on_tors {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)] (ψ ψ' : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (IsLocalRing.maximalIdeal R) fun g => (ψ g : R))
    (hψ' : Alg.AdicCont (IsLocalRing.maximalIdeal R) fun g => (ψ' g : R))
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → ψ g = ψ' g) (g : Dec (F := F) A) (M : ℕ) (hM : 0 < M)
    (hg : g ^ M ∈ (commutator (Dec (F := F) A)).topologicalClosure) : ψ g = ψ' g := by
  have hfg : (IsLocalRing.maximalIdeal R).FG := IsNoetherian.noetherian _
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›
  have hN : ∀ N : ℕ, Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ g : R) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ' g : R) := by
    intro N
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.finite_quotient_pow hfg N
    let mkN : R →* R ⧸ IsLocalRing.maximalIdeal R ^ N :=
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)).toMonoidHom
    let u : Dec (F := F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ
    let u' : Dec (F := F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ'
    have hu : IsLocallyConstant u :=
      IsLocallyConstant.desc _ Units.val (hψ N) (fun _ _ e => Units.ext e)
    have hu' : IsLocallyConstant u' :=
      IsLocallyConstant.desc _ Units.val (hψ' N) (fun _ _ e => Units.ext e)
    have hχN : IsLocallyConstant (u * u'⁻¹) := hu.mul hu'.inv
    have hres := char_tors h (u * u'⁻¹) hχN (by
      intro x hx
      show u x * (u' x)⁻¹ = 1
      have e : u x = u' x := by
        show Units.map mkN (ψ x) = Units.map mkN (ψ' x)
        rw [hI x hx]
      rw [e, mul_inv_cancel]) g M hM hg
    have e2 : u g = u' g := by
      have : u g * (u' g)⁻¹ = 1 := hres
      exact mul_inv_eq_one.mp this
    exact congrArg Units.val e2
  apply Units.ext
  rw [IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp (hN n)

end UpperTheory.V.Hi.JEx
