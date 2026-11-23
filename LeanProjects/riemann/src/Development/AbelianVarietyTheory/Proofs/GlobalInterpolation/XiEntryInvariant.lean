import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.MatLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem exists_lift (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} {b : L.β j} {P : rowSG Pr sel mu}
    {κ : GLint X.E (R.N j) P.1} {c : X.Kˣ} (hk : LevAt (L.levG j b) (L.levQ j b) P κ c) :
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E _ (cOf R j) x) = Loc.inX X.E _ (cOf R j) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨h, rfl⟩ := hk.1 hP
    obtain ⟨g, hg, hred⟩ := (hL.grpG j b ⟨P.1, hP⟩ _).1 h
    have hgi : g ∈ GLint X.E (R.N j) P.1 := hL.int j b P hg
    have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
    have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp j P.1 hP
      (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG j b P hP)
      _ ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ).2 fun x hx => by
        rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
    have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 (L.h j b P) := by
      have := mul_mem hg h2
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrG j b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
  · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    obtain ⟨h, rfl⟩ := hk.2 hP' hP
    have h3 := h
    rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrQ j b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩

theorem muAt_det (i : ℕ) (P : rowSG Pr sel mu) {n : ℕ} (k : GLint X.E n P.1) :
    muAt Ch sel mu cst i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
  unfold muAt rhoS
  refine LastSteps.locChar_unit _ _ ?_
  rw [(det_glint k).2, ← redGL_val]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (redGL _ P.1 k).isUnit

theorem xiEntry_invariant {u : Pr.Word} (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i)
    (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + z) = XiEntry Ch sel mu cst L i al be p p' x := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hz
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiEntry Ch sel mu cst L i al be p p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    refine hL.xiInv i hi al be P _ _ fun s l => ?_
    have h1 : frsF sel mu p P (Pi.single s 1) ∈ p.deco.1.at P.1 :=
      (frsF_mem p P _).2 ((mem_localization_standardLattice _ _).2 (GlobalTheory.TopInv.single_int s))
    have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
    have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E _ P.1 := by
      refine (frsF_mem p' P _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    have h4 := (mem_localization_standardLattice _ _).1 h3 l
    obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
    have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) (Pi.single s 1) l =
        (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) l := by
      change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P (Pi.single s 1))) l = _
      rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
    rw [h5, hc']
    convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
    push_cast
    field_simp

theorem xiEntry_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    {al : L.β i} {be : L.β (i + 1)} {γ : UF X.E (R.N i)} {γ' : UF X.E (R.N (i + 1))} {p q : ChPt (R := R) sel mu u i}
    {p' q' : ChPt (R := R) sel mu u (i + 1)}
    {κ : GLQ X.E (R.N i) (rowSG Pr sel mu)} {κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu)} {a a' : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = γ.1 * (frsF sel mu p P * ((κ P)⁻¹).1))
    (hκ' : ∀ P, frsF sel mu q' P = γ'.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1))
    (ha : ∀ P, LevAt (L.levG i al) (L.levQ i al) P (κ P) (a P))
    (ha' : ∀ P, LevAt (L.levG (i + 1) be) (L.levQ (i + 1) be) P (κ' P) (a' P)) (x : HomE X.E (R.N i) (R.N (i + 1)))
    (e0 : phiT X.K q.deco.1 q'.deco.1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT X.K p.deco.1 p'.deco.1 x) :
    XiEntry Ch sel mu cst L i al be q q' (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
      (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  have hP1 := fun P : rowSG Pr sel mu => UnfoldTwoSided.degOne_bad hX hPr hsel P
  unfold XiEntry
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu q' P) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (κ' P).1.toLinearMap ∘ₗ (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) := by
    rw [hκ, hκ']
    refine LinearMap.ext fun w => ?_
    show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 (x (γ.1.symm (γ.1 (frsF sel mu p P (((κ P)⁻¹).1 w)))))))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨r, hr, hrx, hc⟩ := exists_lift hX hPr hL (ha P).inv
  obtain ⟨r', hr', hrx', hc'⟩ := exists_lift hX hPr hL (ha' P)
  have h1 := UnfoldTwoSided.xiAt_right hP1 hL hi al be P hr hrx (inFr (frsF sel mu p P) (frsF sel mu p' P) x)
  have h2 := UnfoldTwoSided.xiAt_left hP1 hL hi al be P hr' hrx'
    (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap)
  rw [muAt_det, ← hc] at h1
  rw [muAt_det, ← hc'] at h2
  rw [e1, Pi.inv_apply, Pi.inv_apply, rhoT_inv, mul_comm (rhoS _ _ _ _ _ _), ← mul_assoc, h2, mul_assoc, h1, Units.val_mul, mul_assoc]

theorem matEquiv {u : Pr.Word} {T : ChTh W sel mu u m2} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2) (hT : ChTh.Ok (Ch := Ch) cst T) :
    MatEquiv W Ch sel mu cst L T := by
  intro i hi al be g g₁ p p'
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g₁ p'
  have key := GlobalTheory.kerOf_gmap_frames (T.th i) (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _ (hT.th i hi.le) g.1 g₁.1
    p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (XiEntry Ch sel mu cst L i al be p p')
    (XiEntry Ch sel mu cst L i al be (g • p) (g₁ • p')) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (xiEntry_invariant hPr hL hi al be p p') fun x =>
      xiEntry_law hX hPr hsel hL hi hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  unfold matK
  rw [funext hκ, funext hκ']
  refine key.trans ?_
  rw [ea, ea', mul_inv, ← map_inv (L.levG i al).chr, ← map_inv (L.levQ i al).chr]
  exact smul_comp_smul _ _ _ _ _

end GlobalTheory.MatLaw

namespace GlobalTheory.MatLaw

open GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem kAt_equiv : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i + 2 < R.m → ∀ b b' (g : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).G b) (g' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).G b') (d : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).D b) (d' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).D b'), kAt W Ch sel mu cst L A u i b b' (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).actD b; g • d) (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).actD b'; g' • d') = (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).rho X.emb (W.lamTrue u i) b g⁻¹ := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A hX hPr _ hsel hT hg hL _ hTh hi b b' g g' d d'
  have hm := hL.hm
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (Idx.of_get b (by omega) _).symm⟩
  obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
  have e : ∀ p p', kAt W Ch sel mu cst L A u i (Idx.of al (by omega)) (Idx.of be (by omega)) p p' =
      matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) i al be p.1.1 p'.1.1 := fun p p' => by
    rw [matK_eq_xiAt W Ch sel mu cst L _ hi]
    unfold kAt KerT.ker
    rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u i (by omega)]
    rfl
  rw [e, e]
  exact matEquiv hX hPr hsel ⟨hT, hg⟩ hL hTh i (by omega) al be g g' d.1.1 d'.1.1

end GlobalTheory.MatLaw

end
