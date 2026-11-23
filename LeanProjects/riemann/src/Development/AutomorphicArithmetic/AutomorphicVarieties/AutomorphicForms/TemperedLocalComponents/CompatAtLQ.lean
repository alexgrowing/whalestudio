import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Untwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩

private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

private theorem compatK (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 2 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (ha : AttC ι r π)
    {w : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw) :
    IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
      Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (rc (algNorm σ)) := by
  obtain ⟨R, hc, hs, Haw, Hab⟩ := P.ss K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => Haw w hw A h rc hrc σ hσ, hf⟩
  have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) h1.1
  exact ⟨h3.1, fun σ hσ rc hrc => h3.2 ▸ h1.2 σ hσ rc hrc⟩

def CompatAtLQ2 : Prop :=
  ∀ (n : ℕ) [Fact (n = 2)], 2 ≤ n → ∀ (wt : ℤ) (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub ℚ n), Continuous r → IsIrr r →
    ∀ (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Level l M m r →
    (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → π.IsRegAlg → AttR ι r π →
    ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l ℚ Ω (Dec (F := ℚ) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := ℚ) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := ℚ) A).subtype)) (rc (algNorm σ))

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatAtLQ :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.CompatAtLQ2 := by
  intro P n _ hn wt l _ hl Ω _ _ _ ι r π hr hirr M m _ _ _ hdual hreg hatt v A h O _ _ _ Bw hj
  obtain ⟨θ, hθ, hd⟩ := hdual
  obtain ⟨χ₀, hχ₀, -⟩ := selfDualQ P n (by omega) wt l Ω ι r π θ hθ hd hatt
  obtain ⟨r', wt', HT, hG⟩ := P.galR ℚ Ω l ι n (by omega) π χ₀ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hχ₀⟩
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  have hiso : RepIso r' r := by
    refine isoOfFrob P ℚ Ω l ι n r' r hG.cont hr hG.ss hatt.1 ?_
    filter_upwards [hatt.2, eventually_not_mem ℚ l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P ℚ n π w
    exact ⟨_, satFrob P ℚ Ω l ι n r' hG.cont w hw σ B (((satLoc P ℚ n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)
      fun A h rc hrc => hG.away w hw A h rc hrc σ hσ, hf⟩
  have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := ℚ) A).subtype) := by
    obtain ⟨p, hp⟩ := hiso
    obtain ⟨T⟩ := Loc.tiedP l
    exact (GlobalTheory.PstConj.main ℚ Ω l ι n _ _ ⟨T⟩ v A h O Bw hj _ _ p (fun g => hp g)
      (P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hG.cont.comp continuous_subtype_val))
        (hG.above _ _ ⟨T⟩ v A h O Bw hj).1)).1
  refine ⟨hpst, fun σ hσ rc hrc => ?_⟩
  obtain ⟨K, _, _, _, _, _, _, hK, hemb, v₀, A₀, ⟨B₀, -, hB₀⟩, hA₀, s, hs, hs'⟩ := Cq.exQuad Ω l hl _ hatt.2
  obtain ⟨Q, χ, μ₀, hQ, hQa, hpol, ⟨-, -, a, -, hχa, -⟩, -⟩ := Bc.bcPolar P K hK n (by omega) l Ω ι r wt θ π hreg hr hatt hθ hd
    (isIrr_comp (range_of_sign l hK hs' ((hB₀ A₀ hA₀).1 s hs)) hirr)
  have hχa' : IsAlgPos χ⁻¹ (-a) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hχa k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨k, b, hb⟩ := Cq.signFix K hK χ⁻¹ (-a) hχa'
  obtain ⟨κ, mκ, hκ, hκχ⟩ := Cq.extReal K _ b hb
  have hcsd : GlobalTheory.ContraPair.DualIsConj (Q.twist κ) := Cq.csdTwist K n Q _ κ hpol.dual (by
    rw [hκχ, map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, map_inv])
  obtain ⟨artK, hartK, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ mκ (isAlgPos_of_isAlg hκ)
  have hR : Continuous (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    hr.comp (continuous_restrictScalarsHom ℚ K Ω)
  have hjK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := fun x => by
    obtain ⟨y, hy⟩ := Cq.embPadic K hK l hemb (Bw.j.comp (algebraMap K Ω)) x
    exact (hy ▸ Bw.Kw.1.algebraMap_mem y :)
  obtain ⟨Bw', e1, e2, e3⟩ := Cq.exBridge ℚ K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w, h', i, hi⟩ := Cq.exPlaceIso ℚ K Ω l A v h O Bw hj hjK
  obtain ⟨⟨σ', hσ'⟩, -⟩ := locCompC P K n Q w
  obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
  obtain ⟨e, he⟩ := hQ.split hreg ⟨χ₀, fun v v' => by rw [Subsingleton.elim v v'], hχ₀⟩ v w i hi.cont hi.loc σ σ' hσ hσ'
  obtain ⟨c1, c2⟩ := compatK P hn (Bc.irrBasic.2 _ _ n _ μ hR hμc)
    (regAlg_twist ((Br.bcAtt0 ℚ K Ω l ι n r π Q hQ.toIsBC0).1 hreg) hκ) hcsd
    (Cq.attTwist K Ω l ι n _ Q hQa artK κ mκ μ hartK hμ) h' Bw' hj'
  have c3 := Lev.untwistS P.litN.aut.chA P.litN.aut.chW P.litN.aut.berger K Ω l ι n _ hR artK κ mκ μ hartK
    (isAlgPos_of_isAlg hκ) hμc hμ w A h' O Bw' hj' (Cq.pstRes ℚ K Ω l A O Bw Bw' e1 e2 e3 n r hpst) c1 σ' rc' hrc'
    (c2 _ (hσ'.twist κ) rc' hrc')
  refine Lev.recMove hL ℚ K Ω A v w h h' _ i hi n σ σ' e he rc rc' hrc hrc' _ _ ?_ c3
  exact Cq.wdRelRes ℚ K Ω l A O Bw Bw' e1 e2 e3 n r hpst ι v w h h' hj hj' i hi

end
