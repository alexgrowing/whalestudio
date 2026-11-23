import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteGeneralOfOld
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertB

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC GlobalTheory.PRep

namespace UpperTheory.One.M.Ud

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def UnitaryReadS {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A) (rc : RecMap A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w → GlobalTheory.DefiniteBCGood.GoodSplitU U ∧
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BCSupport in

theorem good_of_sph {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (h1 : GlobalTheory.LGrp.IsSpherical (locProd h w σ) (GlobalTheory.LFun.KGL w n)) (i) :
    Good (clsOf (σ i)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
  have h1' : GlobalTheory.LGrp.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) (GlobalTheory.LFun.KGL w n) := isSpherical_of_equiv e h1
  have h3 : GlobalTheory.SmGL.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) :=
    isSphericalFor_of_eq (GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko w n) ((GlobalTheory.LGrp.isSpherical_iff _ _).1 h1')
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ _
    (GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ c n _ h _ _ (IsSubquotient.refl _) h3 i)).2

theorem udPart {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (hMW : DiscCsd H.E) (hT : PositivityTheory.UdReth2.TempCsdP H.E) (hS : PositivityTheory.UdReth2.RecSpehP rc) (hC : CuspReadG rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V)
    (m : (H.E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hnd : ∀ τ, (m τ).Nodup)
    (hg : ∃ g : ℂ, ∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = g + k)
    (hG : ∀ w : PlE H, ∃ σ', IsLocCompGL V w σ' ∧ Good (GlobalTheory.BCSupport.clsOf σ')) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hd : 1 ≤ d := Nat.pos_of_mul_pos_left (had ▸ hn)
  obtain ⟨r1, r2⟩ := PositivityTheory.UdReth.cusp_reg m hm hnd hg hd P h3
  have hPG : ∀ w σ, P.IsLocComp w σ → Good (GlobalTheory.BCSupport.clsOf σ) := fun w σ hσ => by
    obtain ⟨σ', hσ', hg⟩ := hG w
    obtain ⟨-, σ₀, l, -, q⟩ := h2 w σ' hσ'
    have e : GlobalTheory.BCSupport.clsOf σ = GlobalTheory.BCSupport.clsOf σ₀ :=
      GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w σ σ₀ hσ l)
    rw [e]
    exact GlobalTheory.DefiniteBCGood.good_of_isSpehQuot h σ₀ σ' hd q hg
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1 hPG
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
    (hP : RecProd rc) (hS : PositivityTheory.UdReth2.RecSpehP rc) (hSat : RecSatake rc) (hC : CuspReadG rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U)
    (hw : ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam) (hGs : GlobalTheory.DefiniteBCGood.GoodSplitU U)
    (hSat' : ∀ w, ¬ IsSplitPl H w → ∃ α, IsSatAt U w α) :
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
  have hgood : ∀ i w, Good (GlobalTheory.BCSupport.clsOf (σ i w)) := fun i w => by
    by_cases hw : IsSplitPl H w
    · have hc := bc.split w (isSplitAt_of_isSplitPl hw)
      exact GlobalTheory.BCSupport.good_of_good_locProd h w (σ · w) hc.1
        (hGs w hw ⟨_, locProd h w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, hc.1⟩ hc) i
    · obtain ⟨α, s, ϖ, q, e1, e2, e3⟩ := hSat' w hw
      exact good_of_sph h w (σ · w) (bc.unram w (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt e1 e2.2.1 e3)) i
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    Ud.udPart hMW hT hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (m i) (bc.inf i) (hnd i) (hg i)
      (fun w => ⟨σ i w, bc.loc i w, hgood i w⟩)
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

end UpperTheory.One.M.Ud

end
