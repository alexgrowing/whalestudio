import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.InCongruenceModuleJeReCutTOfRestrict
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement

noncomputable section

namespace UpperTheory.GalC.Tr

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows

variable {D : D7} {c : CutD D}

theorem ptV_iff (i : (cut D c).nd.Loc) (P : D.naut.AV i.1) (x : (cut D c).nd.X i) :
    (cut D c).naut.ptV i P = some x ↔ D.naut.ptV i.1 P = some x.1 := optIn_eq_some

theorem par_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) (Sig : List (Part D.naut.CG)) :
    HasParamX (cut D c).nd (cut D c).naut i x Sig ↔ HasParamX D.nd D.naut i.1 x.1 Sig :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zn_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZN D.nd D.naut i.1 :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zg_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZgoodN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZgoodN D.nd D.naut i.1 :=
  and_congr (zn_iff i x) (exists_congr fun Sig => and_congr (par_iff i x Sig) Iff.rfl)

theorem z_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) : x ∈ (cut D c).nd.Z i ↔ x.1 ∈ D.nd.Z i.1 :=
  ((cut D c).Z_tie i x).trans ((zn_iff i x).trans (D.Z_tie i.1 x.1).symm)

theorem hg_of {i : (cut D c).nd.Loc} (h : HG (cut D c).nd (cut D c).naut i) : HG D.nd D.naut i.1 :=
  h.elim fun x hx => ⟨x.1, (zg_iff i x).1 hx⟩

theorem eigC_eq (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    eigC (cut D c).nd (cut D c).naut i x = eigC D.nd D.naut i.1 x.1 := by
  have e : {P | (cut D c).naut.ptV i P = some x} = {P | D.naut.ptV i.1 P = some x.1} := Set.ext fun P => ptV_iff i P x
  unfold eigC
  rw [e]; rfl

theorem res_eq {O X : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O)) [IsLocalRing T] (f : T) (x y : X) :
    IsLocalRing.residue O ((f : X → O) x) = IsLocalRing.residue O ((f : X → O) y) := by
  let g : T := f - algebraMap O T ((f : X → O) x)
  have hx : (g : X → O) x = 0 := by simp [g]
  have hg : ¬ IsUnit g := fun h => by
    have := h.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom) g = 0 := hx
    rw [e] at this
    exact not_isUnit_zero this
  have hy : ¬ IsUnit ((g : X → O) y) := fun h => by
    obtain ⟨u, hu⟩ := h
    let k : T := 1 - algebraMap O T (↑u⁻¹ : O) * g
    have hk : IsUnit k := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (algebraMap O T (↑u⁻¹ : O) * g) with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hg
      · exact h
    have := hk.map ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom) k = 0 := by
      show (1 : O) - (↑u⁻¹ : O) * (g : X → O) y = 0
      rw [← hu, Units.inv_mul, sub_self]
    rw [e] at this
    exact not_isUnit_zero this
  have e : (g : X → O) y = (f : X → O) y - (f : X → O) x := by simp [g]
  rw [e] at hy
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hy

theorem hecke_res (D : D7) (i : D.nd.Loc) (x y : D.nd.X i) (w : PlE D.host) :
    (heckePol D.nd i x w).map (IsLocalRing.residue (D.nd.O i)) = (heckePol D.nd i y w).map (IsLocalRing.residue (D.nd.O i)) := by
  haveI := D.nd.T_local i
  unfold heckePol
  simp only [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, res_eq (D.nd.T i) _ x y]

theorem atM_iff (i : (cut D c).nd.Loc) (σ : D.what₂.FT) : AtM (cut D c).nd (cut D c).naut i σ ↔ AtM D.nd D.naut i.1 σ := by
  refine exists_congr fun Sig => and_congr Iff.rfl ⟨fun ⟨x, h⟩ => ⟨x.1, h⟩, fun ⟨x, h⟩ => ?_⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  refine ⟨y, fun w hw => ?_⟩
  obtain ⟨p, h1, h2⟩ := h w hw
  exact ⟨p, h1, h2.trans (hecke_res D i.1 x y.1 w)⟩

theorem rhoBar_iff (i : (cut D c).nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i.1))) :
    IsRhoBar (cut D c).nd i rb ↔ IsRhoBar D.nd i.1 rb := by
  refine and_congr Iff.rfl ⟨fun h x w hw B σ hB hσ => ?_, fun h x => h x.1⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  exact (h y w hw B σ hB hσ).trans (hecke_res D i.1 y.1 x w)

theorem goodPart_eq (i : (cut D c).nd.Loc) : goodPartM (cut D c).nd (cut D c).naut i = goodPartM D.nd D.naut i.1 := by
  have e : {σ | (cut D c).nd.goodRow σ ∧ AtM (cut D c).nd (cut D c).naut i σ} = {σ | D.nd.goodRow σ ∧ AtM D.nd D.naut i.1 σ} :=
    Set.ext fun σ => and_congr Iff.rfl (atM_iff i σ)
  unfold goodPartM
  rw [e]; rfl

theorem iSup_good (hc : c.Good) (i : (cut D c).nd.Loc) {α : Type} [CompleteLattice α] (F : D.nd.X i.1 → α) :
    ⨆ x ∈ ZgoodN (cut D c).nd (cut D c).naut i, F x.1 = ⨆ x ∈ ZgoodN D.nd D.naut i.1, F x :=
  le_antisymm (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun x _ => F x) x.1 ((zg_iff i x).1 hx) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun (x : (cut D c).nd.X i) _ => F x.1)
      ⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hx)⟩ ((zg_iff i _).2 hx) le_rfl)

theorem tie0_cut_of_tie0 (h : SumRepresentations.tie0 D) : SumRepresentations.tie0 (cut D c) :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, fun i => h.2.1.2.2.2 i.1⟩,
    fun i => h.2.2.1 i.1, fun i => h.2.2.2.1 i.1, fun i => h.2.2.2.2.1 i.1, fun i => h.2.2.2.2.2 i.1⟩

theorem fourthAdmissible_restrictToPoints (h : SumRepresentations.ArchimedeanSignatureMatching D) : SumRepresentations.ArchimedeanSignatureMatching (cut D c) := ⟨fun i => h.1 i.1, fun i => h.2.1 i.1, h.2.2⟩
theorem hypO_cut (h : SumRepresentations.hypO D) : SumRepresentations.hypO (cut D c) := fun i x => h i.1 x.1
theorem rhoBar_cut (h : ResidualIrreducibleRankR D) : ResidualIrreducibleRankR (cut D c) := fun i hg rb hrb => h i.1 (hg_of hg) rb ((rhoBar_iff i rb).1 hrb)

theorem rowsB_cut (h : RowsB D) : RowsB (cut D c) :=
  { rowSize := fun i => h.rowSize i.1, a3 := fun i => h.a3 i.1, a4 := fourthAdmissible_restrictToPoints h.a4, thetaOne := fun i => h.thetaOne i.1 }

theorem rowsC_cut (hc : c.Good) (h : RowsC D) : RowsC (cut D c) :=
  { c4b := fun σ k v h1 h2 i => h.c4b σ k v h1 h2 i.1
    rho := fun i x hx Sig hS => h.rho i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    dz := fun i x hx Sig hS => h.dz i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    parUp := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.parUp i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    downMem := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.downMem i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    goodPart := fun i => by
      refine (goodPart_eq i).trans ((h.goodPart i.1).trans ((iSup_good hc i _).symm.trans ?_))
      refine iSup_congr fun x => iSup_congr fun _ => ?_
      have e : {Sig | HasParamX (cut D c).nd (cut D c).naut i x Sig} = {Sig | HasParamX D.nd D.naut i.1 x.1 Sig} :=
        Set.ext fun Sig => par_iff i x Sig
      rw [e]; rfl }

set_option maxHeartbeats 1000000 in

def ledBack (L : SizeData₂ (cut D c)) : SizeData₂ D := { L with }

theorem pointsAdmissible_restrictToPoints (hc : c.Good) (h : SumRepresentations.ConclusionZ D) : SumRepresentations.ConclusionZ (cut D c) := by
  classical
  intro i hg
  obtain ⟨a, b, d⟩ := h i.1 (hg_of hg)
  refine ⟨fun x hx Sig hS => ?_, ?_, ?_⟩
  · rw [eigC_eq]; exact a x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
  · rw [goodPart_eq]
    refine b.trans ((iSup_good hc i _).symm.trans (iSup_congr fun x => iSup_congr fun _ => (eigC_eq i x).symm))
  · have e : dM (cut D c).nd (cut D c).naut i = dM D.nd D.naut i.1 := by unfold dM; rw [goodPart_eq]; rfl
    rw [e, ← d]
    refine Finset.sum_of_injOn (fun x => x.1) (fun x _ y _ k => Subtype.ext k) (fun _ _ => Finset.mem_univ _)
      (fun x _ hx => if_neg fun hz => hx ⟨⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hz)⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      fun x _ => ?_
    have m : (cut D c).nd.mult i x = D.nd.mult i.1 x.1 := Alg.mult_eq _ _ _ (D.nd.T_sep i.1) x
    by_cases hz : x.1 ∈ ZgoodN D.nd D.naut i.1
    · rw [if_pos hz, if_pos ((zg_iff i x).2 hz), m]
    · rw [if_neg hz, if_neg fun k => hz ((zg_iff i x).1 k)]

theorem jointCondition_restrictToPoints (h : KillingConditions.LocalisationUniqueness D) : KillingConditions.LocalisationUniqueness (cut D c) :=
  fun i i' h1 h2 h3 σ hσ a b => Subtype.ext (h i.1 i'.1 h1 h2 h3 σ hσ ((atM_iff i σ).1 a) ((atM_iff i' σ).1 b))

theorem live_of {i : (cut D c).nd.Loc} (h : GlobalTheory.CoefDuty.Live (cut D c).nd i) : GlobalTheory.CoefDuty.Live D.nd i.1 := by
  obtain ⟨π, hπ, k⟩ := h
  exact ⟨π.1, (z_iff i π).1 hπ, k⟩

theorem large_cut (h : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large (cut D c) := by
  refine ⟨hypO_cut h.1, fun i x => h.2.1 i.1 x.1, fun i hl => ?_⟩
  obtain ⟨r, ρ, hr, A, i1, i2, i3, i4, i5, i6, i7, TA, repA, ρA, χA, hE, hS, hC⟩ := h.2.2 i.1 (live_of hl)
  haveI : Nonempty (c.Xs i.1) := (c.ne i.1 i.2).to_subtype
  refine ⟨fun x => r x.1, fun x => ρ x.1, fun x => hr x.1, A, i1, i2, i3, i4, i5, i6, i7, Alg.cutT TA (c.Xs i.1),
    fun x => repA x.1, fun x => ρA x.1, χA,
    ⟨hE.1, span_cut (O := D.nd.O i.1) (TO := D.nd.T i.1) (c.Xs i.1) hE.2.1, fun x => hE.2.2.1 x.1, fun x hx => hE.2.2.2.1 x.1 ((z_iff i x).1 hx), hE.2.2.2.2⟩,
    setting_cut _ (fun y hy => (z_iff i y).1 hy) hS, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, a, b, d⟩ := hC π.1 ((z_iff i π).1 hπ)
  exact ⟨g0, L, fun y => eB y.1, fun y => e1 y.1, fun y => X0 y.1, a, isChoice_cut _ b, fun x => d x.1⟩

theorem cutRec_cut (hc : c.Good) : CutRec (cut D c) := by
  intro i P hP k w hw
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  exact hc.nice i.1 i.2 P x.1 x.2 ((ptV_iff i P x).1 hx) k w hw

end UpperTheory.GalC.Tr
