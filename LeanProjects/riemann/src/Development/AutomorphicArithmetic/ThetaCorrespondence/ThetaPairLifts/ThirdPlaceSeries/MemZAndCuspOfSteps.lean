import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TwListSs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem mem_ZN_alt (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (h2 : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight') (h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (h8 : EigenCharTwist)
    (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount) (h11 : Numerics) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (x : D.nd.X i) (v : Fin D.R.nV → Kf D.nd i) (hv0 : v ≠ 0)
    (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    x ∈ ZN D.nd D.naut i := by
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hBC⟩ := hA.1.1.2.2.1 i P
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    (GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)).2.1
  obtain ⟨p, hpL, u, hu0, hu⟩ := h8 (Qbar (D.nd.l i)) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.nV
    (mapRep (iotaOQ D.nd D.naut i) (r x)) (twList D i Pa R) (cU D i) hss (_root_.GlobalTheory.EigenPoint.isSSRep_of_mem_twList D i Pa R hR)
    (fun g => (hcp g).trans (twList_cp D i Pa R g).symm) (eig_map D i (r x) v hv0 hv)
  obtain ⟨k, a, ha, rfl⟩ := mem_twList D i hpL
  have hW : ∀ g, ((epsQ D i g)⁻¹ ^ a) • ((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
      (Qbar (D.nd.l i))).mulVec u = iotaOQ D.nd D.naut i (chi1 D.nd i g) • u := fun g => by
    have e := hu g
    rw [twGL_val, Matrix.smul_mulVec, eU_pow] at e
    exact e
  have hwt := h2 D hA i x P Pa hP hBC k (R k) (hR k) a ha ⟨u, hu0, hW⟩
  have hmem : Pa.get k ∈ Pa := List.get_mem Pa k
  have ha1 : 1 ≤ (Pa.get k).a := (hBC.1 _ hmem).1
  have hr1 : 1 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k
    show 1 < D.R.k + D.R.m - 1
    omega
  have ht2 : 2 ≤ D.R.t := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; have := D.R.rank_add_five_le
    omega
  have hle : (Pa.get k).d • Ak k ≤ D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact Multiset.le_add_right _ _
  have hnum := h11 D.R.r D.R.t (Pa.get k).d (Pa.get k).a a (Ak k) hr1 ht2 ha hwt (hAk k).1 (hAk k).2 ha1 hle
  have ha0 : a = 0 := by rw [hnum.2] at hwt; omega
  subst ha0
  have hpart := _root_.GlobalTheory.EigenPoint.eq_one_twist_t_of_mulVec_eigen D i h3 h4 hA hg (Pa.get k) (R k) (hR k) hnum.1 hnum.2 u hu0
    (fun g => by simpa using hW g)
  exact ⟨P, hP, Pa, hBC, hpart ▸ hmem⟩
theorem isCuspIso_of_hasParamX (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount)
    (h12 : Rest) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (Sig : List (Part D.naut.CG)) (hSig : HasParamX D.nd D.naut i x Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨P, hP, hBC⟩ := hSig
  have hlen : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).length = Sig.length + 1 := by
    simp [twistIso]
  have hlast : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).get
      (Fin.cast hlen.symm (Fin.last _)) = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]
    simp [twistIso, muPart, List.getElem_append_right]
  generalize hPa : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv = Pa at hBC hlen hlast
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  rw [sum_split hlen] at hsum
  have hAl : Ak (Fin.cast hlen.symm (Fin.last _)) = {1} :=
    ms_one ((hAk _).1.trans (by rw [hlast])) (hAk _).2
  have hlt : (Pa.get (Fin.cast hlen.symm (Fin.last _))).d • Ak (Fin.cast hlen.symm (Fin.last _)) =
      Multiset.replicate D.R.t 1 := by
    rw [hAl, hlast]
    exact Multiset.nsmul_singleton _ _
  rw [hlt, ← Multiset.singleton_add] at hsum
  have hS := add_right_cancel hsum
  have hmem : ∀ k : Fin Sig.length, Pa.get (Fin.cast hlen.symm k.castSucc) ∈ Pa := fun k => List.get_mem _ _
  have hG := h12 (Fin Sig.length) (fun k => (Pa.get (Fin.cast hlen.symm k.castSucc)).d)
    (fun k => Ak (Fin.cast hlen.symm k.castSucc)) D.R.r (fun k => (hBC.1 _ (hmem k)).2.1)
    (fun k h => by
      have e := (hAk (Fin.cast hlen.symm k.castSucc)).1
      rw [h, Multiset.sum_zero] at e
      have := (hBC.1 _ (hmem k)).1
      omega) hS
  have hl1 : Sig.length = 1 := by simpa using hG.1
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl1
  have h0 := hG.2 ⟨0, by simp⟩
  have hget : Pa.get (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length))) =
      ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ := by
    subst hPa
    simp [twistIso]
  have hd : p.d = 1 := by have := h0.1; rw [hget] at this; exact this
  have ha : p.a = D.R.r := by
    have e := (hAk (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length)))).1
    rw [h0.2, hget, Multiset.sum_singleton] at e
    exact e.symm
  rcases p with ⟨a, π, d⟩
  dsimp only at hd ha
  subst hd ha
  exact ⟨π, rfl⟩
theorem prvG6_of_realisation_mu_res_count_numerics : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D :=
  fun h1 h2 h3 h4 h8 hrc h11 h12 D hA hRb i hg r hr x hx =>
    ⟨hx.elim fun v hv => _root_.GlobalTheory.EigenPoint.mem_ZN_alt D i h1 h2 h3 h4 h8 hrc h11 hA hRb hg r hr x v hv.1 hv.2,
      fun Sig hSig => _root_.GlobalTheory.EigenPoint.isCuspIso_of_hasParamX D i h1 hrc h12 hA hRb hg r hr x Sig hSig⟩
end GlobalTheory.EigenPoint
end
end
