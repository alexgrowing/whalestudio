import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

scoped macro "obt " p:Lean.Parser.Tactic.rcasesPatMed " := " e:term : tactic => `(tactic| (have x := $e; obtain $p := x))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_measY (t : T) (j : ℕ) : ∃ (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
    (j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) ∧
    (j = D.R.m - 1 → IsMeasDef (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) := by
  have hLev := GlobalTheory.Mem.LevelOK.levOK_all D
  by_cases hj : j = D.R.m - 1
  · subst hj
    obtain ⟨μ, 𝓕, hμ⟩ := measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D)
      (Yc D (D.R.m - 1)) _ (D.sp.Y_sig _) (GlobalTheory.Mem.EasyInputs.spOK D).1
      (hLev _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)).1
    exact ⟨μ, 𝓕, fun h2 => absurd h2 (by omega), fun _ => hμ⟩
  · obtain ⟨μ, 𝓕, hμ⟩ := Formalism.IndefR.Eqv.measFDExists_holds D (Yc D j) (D.sp.Y_sig _) _ (hLev _ (R.βY j) (R.datYt t j R.triv)).1
    exact ⟨μ, 𝓕, fun _ => hμ, fun h' => absurd h' hj⟩

theorem exists_measX (t : T) : ∃ μ 𝓕, IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) D.sp.X' _ D.sp.X'_sig
    (GlobalTheory.Mem.EasyInputs.spOK D).2 (GlobalTheory.Mem.LevelOK.levOK_all D _ R.βX (R.datXt t)).1

theorem exists_measV (hv : ∀ i, (Vc D i).IsPosDef) (i : Fin D.R.m) (t : T) :
    ∃ μ 𝓕, IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) (Vc D i) _ (D.sp.V_sig _)
    (fun τ => Or.inl (hv i τ)) (GlobalTheory.Mem.LevelOK.levOK_all D _ (R.βV i) (R.datVt i t)).1

set_option maxHeartbeats 1000000 in

theorem exists_modX (t : T) : ∃ (H : HMod (Bridge.Gf D.sp.X' → R.cX.W)) (j : A.fam.amb.FR t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ)
      (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) ∧ ∀ x, H.e (j x) = R.B.jR t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ) (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := R.cX.W) (R.B.R t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.R t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jR t) (fun x => by exact (R.B.R t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

set_option maxHeartbeats 1000000 in

theorem exists_modV (i : Fin D.R.m) (t : T) :
    ∃ (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
        (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
    ∀ x, H.e (j x) = R.B.jL i t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := (R.cV i).W) (R.B.L i t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.L i t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jL i t) (fun x => by exact (R.B.L i t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

variable {R}

open Classical in
theorem idem_of_is {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) :
    Disjoint L.Pg (L.Q t) ∧ ∃ e : AE D, IsIdemSum e (L.Pg ∪ L.Q t) :=
  ⟨(GlobalTheory.ChainEquiv.places_sep L μ0 hL t).2, GlobalTheory.CentralShift.exists_idemSum _ fun _ hP _ hP' =>
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')⟩

theorem sd_of_frame {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc, hc.1⟩

theorem exists_kerY (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T) (k : ℕ)
    (hv : k + 1 < D.R.m → IsVacO R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k)) :
    ∃ ω v, k + 1 < D.R.m → IsWeilDatumO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1))
        (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) v := by
  by_cases hk : k + 1 < D.R.m
  · have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).1 k hk
    obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D k) (Yc D (k + 1)) _ _
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    have s1 := sd_of_frame (hL.βY k (by omega))
    have s2 := sd_of_frame (hL.βY (k + 1) hk)
    obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
      (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vac k) (hv hk)
    exact ⟨ω, v, fun _ => ⟨hω, hv'⟩⟩
  · exact ⟨1, 0, fun h => absurd h hk⟩

theorem exists_kerX (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T)
    (hv : IsVacO R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX) :
    ∃ ω v, IsWeilDatumO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX
        (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) R.vacX v := by
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.1
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D (D.R.m - 1)) D.sp.X' _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βY _ hm)
  have s2 := sd_of_frame hL.βX
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
    (idem_of_is hL t).1 (idem_of_is hL t).2 R.vacX hv
  exact ⟨ω, v, hω, hv'⟩

theorem exists_kerP (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (i : Fin D.R.m) (t : T)
    (hv : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i)) :
    ∃ ω v, IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ω ∧
      IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
        R.Pg (R.Q t) (R.xiR t) (R.vacP i) v := by
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.2 i
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Vc D i) (Wc D i) _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βV i)
  have s2 := sd_of_frame (hL.βW i)
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2 (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vacP i) hv
  exact ⟨ω, v, hω, hv'⟩

end GlobalTheory.TupExt

end
