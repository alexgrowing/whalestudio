import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.CentralCharacterLocalHolds
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.SqPowMulInvDivPowEqProdPow

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem conj_conj' (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D x
  have h2 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D (D.host.conj x)
  let _ := D.host.cmStar
  rw [← h2, ← h1, star_star]

theorem cO_coe (D : D7) (x : 𝓞 D.host.E) : ((cO D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem lowB_YY (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : admitted D N N' L L') :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ LowB d (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨M, hM, hlow⟩ := FL.YY_lower D L L' h.2.2.1 h.2.2.2
  refine ⟨(M : 𝓞 D.host.E), by exact_mod_cast hM, fun A => ?_⟩
  have := hlow (A.map (algebraMap (𝓞 D.host.E) D.host.E)) (fun i j => (A i j).isIntegral_coe)
  simpa using this

theorem halvesRec_of_facts (hG : GenHalves) (hLa : LaEqMap) (hMM : MMeq) (hPhi : PhiInj) (hU : UnifElt)
    (hC : CcLoc) (hEq : EqOffBound) (hYY : YYBound) (hUA : UAdm) (hUY : UYY) (hGD : GoodDual)
    (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec := by
  intro D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP s hs
  classical
  obtain ⟨π, hπ0, hπP, hcop, hπb⟩ := hU D P hP
  obtain ⟨γ, hγ0, hγI, t, htP, ht⟩ := hC D cc hcc P

  have key : ∀ {M : ℕ} (Lx Ly : Submodule (𝓞 D.host.E) (Fin M → D.host.E)) (j : ℕ),
      (∀ x ∈ Lx, (π * cO D π) ^ j • x ∈ Ly) → ∀ k, j ≤ k → ∀ x ∈ Lx, (π * cO D π) ^ k • x ∈ Ly := by
    intro M Lx Ly j h k hk x hx
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul]
    exact Ly.smul_mem _ (h x hx)
  have hb : ∀ q ∈ s, ∃ j : ℕ, ∀ k, j ≤ k → (∀ x ∈ q.1, (π * cO D π) ^ k • x ∈ L₀) ∧
      (∀ x ∈ L₀', (π * cO D π) ^ k • x ∈ q.2) ∧ (∀ x ∈ q.2, (π * cO D π) ^ k • x ∈ L₀') ∧
      (∀ x ∈ L₀, (π * cO D π) ^ k • x ∈ q.1) := by
    intro q hq
    obtain ⟨j1, h1, h2⟩ := hEq D P π hπP N q.1 L₀ (hs q hq).2.1
    obtain ⟨j2, h3, h4⟩ := hEq D P π hπP N' q.2 L₀' (hs q hq).2.2
    exact ⟨j1 + j2, fun k hk => ⟨key _ _ _ h1 _ (by omega), key _ _ _ h4 _ (by omega),
      key _ _ _ h3 _ (by omega), key _ _ _ h2 _ (by omega)⟩⟩
  choose! jf hjf using hb
  set J := s.sup jf with hJ
  set w : 𝓞 D.host.E := (π * cO D π) ^ J with hw
  have hwb : ∀ q ∈ s, (∀ x ∈ q.1, w • x ∈ L₀) ∧ (∀ x ∈ L₀', w • x ∈ q.2) ∧ (∀ x ∈ q.2, w • x ∈ L₀') ∧
      (∀ x ∈ L₀, w • x ∈ q.1) := fun q hq => hjf q hq J (Finset.le_sup hq)

  let Yf : Option {q // q ∈ s} → Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
    fun o => match o with
      | none => YYl D L₀ L₀'
      | some q => YYl D q.1.1 q.1.2
  have hww : (π * cO D π) ^ (J + J) = w * w := by rw [pow_add]
  have hbd1 : ∀ o, ∀ y ∈ YYl D L₀ L₀', (π * cO D π) ^ (J + J) • y ∈ Yf o := by
    intro o y hy
    rw [hww]
    match o with
    | none => exact Submodule.smul_mem _ _ hy
    | some q => exact hYY D w N N' q.1.1 L₀ q.1.2 L₀' (hwb q.1 q.2).1 (hwb q.1 q.2).2.1 y hy
  have hbd2 : ∀ o, ∀ y ∈ Yf o, (π * cO D π) ^ (J + J) • y ∈ YYl D L₀ L₀' := by
    intro o y hy
    rw [hww]
    match o with
    | none => exact Submodule.smul_mem _ _ hy
    | some q => exact hYY D w N N' L₀ q.1.1 L₀' q.1.2 (hwb q.1 q.2).2.2.2 (hwb q.1 q.2).2.2.1 y hy
  have hlow : ∀ o, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ LowB d (Yf o : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
    intro o
    match o with
    | none => exact lowB_YY D L₀ L₀' hAdm
    | some q => exact lowB_YY D q.1.1 q.1.2 (hs q.1 q.2).1
  have HG := hG (𝓞 D.host.E) D.host.E P (Fin N') (Fin N) (ccE D cc) γ t π (cO D π) (J + J)
    (Option {q // q ∈ s}) (YYl D L₀ L₀') Yf hγ0 hγI htP ht hπ0 hπP hπb hcop (lowB_YY D L₀ L₀' hAdm) hlow hbd1 hbd2
  have hπE0 : algebraMap (𝓞 D.host.E) D.host.E π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hπ0
  have hπbE0 : algebraMap (𝓞 D.host.E) D.host.E (cO D π) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    rintro h0; exact hπb (h0 ▸ P.asIdeal.zero_mem)
  set u : D.host.E := (algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π) ^ (J + J)
    with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ (div_ne_zero hπbE0 hπE0)
  have hc1 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = algebraMap (𝓞 D.host.E) D.host.E π :=
    conj_conj' D _
  have hc2 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E π) = algebraMap (𝓞 D.host.E) D.host.E (cO D π) := rfl
  have hu1 : u * D.host.conj u = 1 := by
    rw [hu, map_pow, map_div₀, hc1, hc2, ← mul_pow]
    have e : algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π *
        (algebraMap (𝓞 D.host.E) D.host.E π / algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = 1 := by
      field_simp
    rw [e, one_pow]
  have hu1' : u⁻¹ * D.host.conj u⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hu1, inv_one]
  have hinj : Function.Injective (Phi D cc δ N N') := hPhi D cc δ N N' hδ0
  have hAdmA := hUA D N N' L₀ L₀' u hu1 hAdm
  have hAdmB := hUA D N N' L₀ L₀' u⁻¹ hu1' hAdm
  have hLaeq : ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      La D (tor0 D cc δ) L L' = (ccE D cc • YYl D L L').toAddSubgroup.map (Phi D cc δ N N') := fun L L' => by
    rw [hLa, hMM]
  have hAeq : La D (tor0 D cc δ) L₀ (sLat D u L₀') =
      (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, hUY D N N' L₀ L₀' u hu0]
  have hBeq : La D (tor0 D cc δ) L₀ (sLat D u⁻¹ L₀') =
      (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, hUY D N N' L₀ L₀' u⁻¹ (inv_ne_zero hu0)]
  obtain ⟨hHerm, -, -, -, hSC⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  have hIA := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmA
  have hIB := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmB
  have intOf : ∀ Λ : AddSubgroup (VC D N N'), IO.HfInt (tor0 D cc δ) Λ →
      ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, altE (HfS D (tor0 D cc δ) N N') x y = m := by
    intro Λ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    exact ⟨b, by simp only [altE, HfS_apply, hab]; simp⟩
  have good : ∀ (o : Option {q // q ∈ s}) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → YYl D L L' = Yf o →
      GoodLat (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
        ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N'))
        ((ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) (La D (tor0 D cc δ) L L') := by
    intro o L L' hLL hY
    obtain ⟨c1, c2, -, -, -⟩ := HG o
    have hΛ : La D (tor0 D cc δ) L L' = (ccE D cc • Yf o).toAddSubgroup.map (Phi D cc δ N N') := by
      rw [hLaeq, hY]
    have hsum : La D (tor0 D cc δ) L L' ≤
        (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) ⊔
        (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) := by
      rw [hΛ]
      intro z hz
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hz
      obtain ⟨a, ha, b, hb, rfl⟩ := c1 y hy
      rw [map_add]
      exact AddSubgroup.add_mem_sup
        ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).2⟩
        ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).2⟩
    have hsd : ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, altE (HfS D (tor0 D cc δ) N N') v y = b) →
        v ∈ La D (tor0 D cc δ) L L' :=
      fun v hv => hB D cc hcc δ hδ hδ0 N N' L L' hLL v hv
    obtain ⟨d1, d2⟩ := hGD (VC D N N') (HfS D (tor0 D cc δ) N N') _ _ _ hHerm (intOf _ (hAeq ▸ hIA))
      (intOf _ (hBeq ▸ hIB)) hsum hsd
    refine ⟨hSC _ (hA D cc hcc δ hδ hδ0 N N' L L' hLL), hsum, ?_, d1, d2⟩
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := AddSubgroup.mem_map.1 hb
    rw [hΛ] at hab ⊢
    rw [← map_add, AddSubgroup.mem_map_iff_mem hinj] at hab
    exact AddSubgroup.mem_map_of_mem _ (c2 a' ha' b' hb' hab)
  have einf : ∀ X Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E),
      (X ⊓ Y).toAddSubgroup = X.toAddSubgroup ⊓ Y.toAddSubgroup := fun X Y => rfl
  let φ : ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) →
      Matrix (Fin N') (Fin N) (EP D P) :=
    fun a => matI P ((algebraMap (𝓞 D.host.E) D.host.E γ)⁻¹ • Function.invFun (Phi D cc δ N N') (a : VC D N N'))
  refine ⟨_, _, φ, hAeq ▸ hSC _ hIA, hBeq ▸ hSC _ hIB, good none L₀ L₀' hAdm rfl, fun q hq => ?_⟩
  have hq' := hs q hq
  obtain ⟨-, -, c3, c4, c5⟩ := HG (some ⟨q, hq⟩)
  refine ⟨good (some ⟨q, hq⟩) q.1 q.2 hq'.1 rfl, ?_, ?_, ?_⟩
  · haveI := IO.La_index_finite cc hcc δ L₀ q.1 L₀' q.2 hAdm hq'.1
    exact AddSubgroup.index_ne_zero_of_finite
  · intro a
    obtain ⟨a', ha', hΦa⟩ := AddSubgroup.mem_map.1 a.2
    have hinv : Function.invFun (Phi D cc δ N N') (a : VC D N N') = a' := by
      rw [← hΦa]; exact Function.leftInverse_invFun hinj a'
    change _ ↔ matI P ((algebraMap (𝓞 D.host.E) D.host.E γ)⁻¹ •
      Function.invFun (Phi D cc δ N N') (a : VC D N N')) ∈ _
    rw [hinv, ← hΦa, hLaeq, AddSubgroup.mem_map_iff_mem hinj, YP_eq]
    exact c3 a' ha'
  · rw [volP, volA, hLaeq, hLaeq, ← AddSubgroup.map_inf_eq _ _ _ hinj, ← AddSubgroup.map_inf_eq _ _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      YP_eq, YP_eq, ← einf, ← einf]
    have c4' := c4
    have c5' := c5
    simp only [AddSubgroup.relIndex] at c4' c5' ⊢
    rw [c4', c5']

theorem halvesRec_of_clos (hC : ClosChar) (hAp : ApproxLow) (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec :=
  halvesRec_of_facts (genHalves_of hC hAp) lattice_equality_map_holds multiplicity_equality_holds phi_injective_holds uniformizer_element_holds central_character_local_holds
    equality_off_boundary_holds pairing_bound_holds admissible_unipotent_holds unipotent_pairing_holds good_duality_holds hA hB

end Formalism.L2.PairingIndexBounds.Rec
