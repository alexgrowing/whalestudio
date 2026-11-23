import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSpeh
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.BaseChangeDefiniteOfCmDatumRecLaws
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.DiscreteSpectrumUnitarityOfKnownTheorems

noncomputable section

section Ud

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN

namespace UpperTheory.BaseChangeIdentities

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem udPart {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (hMW : DiscCsd H.E) (hT : PositivityTheory.UdReth2.TempCsdP H.E) (hS : PositivityTheory.UdReth2.RecSpehP rc) (hC : CuspRead rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V)
    (m : (H.E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hnd : ∀ τ, (m τ).Nodup)
    (hg : ∃ g : ℂ, ∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = g + k) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hd : 1 ≤ d := Nat.pos_of_mul_pos_left (had ▸ hn)
  obtain ⟨r1, r2⟩ := PositivityTheory.UdReth.cusp_reg m hm hnd hg hd P h3
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1
  refine ⟨⟨a, π, d⟩, ha, hd, c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, -, q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h σ σ' (hT a P ha h1 r1 r2 w σ l) q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m0, hm0, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m0 hm0]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem udParts {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (hNT : DefiniteN)
    (hMW : DiscCsd H.E) (hT : PositivityTheory.UdReth2.TempCsdP H.E)
    (hP : RecProd rc) (hS : PositivityTheory.UdReth2.RecSpehP rc) (hSat : RecSatake rc) (hC : CuspRead rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U)
    (hw : ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  have hnd : ∀ i τ, (m i τ).Nodup := fun i τ => by
    obtain ⟨lam, hl⟩ := hw τ
    have e := bc.weight τ lam hl
    have hle : m i τ ≤ ∑ j, m j τ :=
      Finset.single_le_sum (f := fun j => m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    exact Multiset.nodup_of_le hle (e ▸ nodup_infOfWeight lam)
  have hg : ∀ i, ∃ g : ℂ, ∀ τ, ∀ z ∈ m i τ, ∃ k : ℤ, z = g + k := fun i => by
    refine ⟨((n : ℂ) - 1) / 2, fun τ z hz => ?_⟩
    obtain ⟨lam, hl⟩ := hw τ
    have e := bc.weight τ lam hl
    have hle : m i τ ≤ ∑ j, m j τ :=
      Finset.single_le_sum (f := fun j => m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hz' : z ∈ infOfWeight lam := e ▸ Multiset.mem_of_le hle hz
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hz'
    exact ⟨lam.w k - (k : ℕ), by push_cast; ring⟩
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    udPart hMW hT hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (m i) (bc.inf i) (hnd i) (hg i)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

end UpperTheory.BaseChangeIdentities

end Ud

section Pr

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN

namespace UpperTheory.BaseChangeIdentities

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] host_isCMField

theorem part {rc : RecMap A} (hMW : DiscCsd H.E) (hS : RecSpeh rc) (hC : CuspRead rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1
  refine ⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, u', q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m, hm, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m hm]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem parts {rc : RecMap A} (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspRead rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

theorem bcAt (B : NBC A) (rc : RecMap A) (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspRead rc) (hU : UnitaryRead B rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.BaseChangeDefinite_at B := by
  intro j h1 h2 π hπ
  obtain ⟨U, u1, u2, u3, u4⟩ := hU j h1 h2 π
  have hn : 1 ≤ R.nV := by
    have := R.rank_add_five_le
    simp only [Ranks.nV]
    omega
  obtain ⟨Pa, a1, a2, a3, a4, a5⟩ := parts hNT hMW hP hS hSat hC hn u1
  refine ⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩
  · obtain ⟨lam, hl, -⟩ := u4 H.φ₀
    exact (a5 _ lam hl).1
  · obtain ⟨σ, s1, s2⟩ := a3 w hw
    rw [s2, u2 w hw σ s1]
  · obtain ⟨α, s1, s2⟩ := u3 w hw (hπ w hw)
    rw [s2]
    exact a4 w α s1
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.1]
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.2]

section Frozen

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions

theorem baseChangeDefinite_of_cmDatum_recLaws : ∀ (D : D7) (rc : RecMap D.naut), DefiniteN →
    DiscCsd D.host.E → RecProd rc → RecSpeh rc →
    RecSatake rc → CuspRead rc → UnitaryRead D.nbc rc → SphericalInertData.Conclusion1 D := by
  intro D rc hNT hMW hP hS hSat hC hU _ _ j h1 h2 _ _ π hπ
  obtain ⟨Pa, hPa⟩ := bcAt D.nbc rc hNT hMW hP hS hSat hC hU j h1 h2 π hπ
  exact ⟨Pa, GlobalTheory.DefiniteBCFrozen.isBC_of_isBaseChange hPa⟩

end Frozen

section Closing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField
  IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem baseChange_preserves_unitary_of (hA : AscComp) : DefiniteN → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
      CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D := by
  intro hNT hGU hSC hL D T A hCG hAU
  obtain ⟨hP, hS, hSat⟩ := GlobalTheory.T.rec_product_speh_satake hGU hSC hL D.nd D.naut T
  exact baseChangeDefinite_of_cmDatum_recLaws D (recT T hL) hNT
    (discCsd_of hA D.host.E) hP hS hSat
    (GlobalTheory.T.cuspidal_of_local_langlands hL D T hCG) (GlobalTheory.T.unitary_of_local_langlands hL D T A hAU)

end Closing

end UpperTheory.BaseChangeIdentities

end Pr

end
