import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WitCong

open IsDedekindDomain Formalism.L2.SG.Pf.BBTie

theorem dvd_of_loc {E : Type} [Field E] [NumberField E] {g c : 𝓞 E} (hg : g ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s, s ∉ P.asIdeal ∧ g ∣ s * c) : g ∣ c := by
  classical
  let J : Ideal (𝓞 E) := Submodule.comap (LinearMap.mulRight (𝓞 E) c) (Ideal.span {g})
  have hJ : ∀ s, s ∈ J ↔ g ∣ s * c := fun s => by
    simp [J, Submodule.mem_comap, Ideal.mem_span_singleton]
  by_contra hnd
  have hJtop : J ≠ ⊤ := by
    intro htop
    apply hnd
    have h1 : (1 : 𝓞 E) ∈ J := htop ▸ Submodule.mem_top
    simpa using (hJ 1).1 h1
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
  have hgJ : g ∈ J := (hJ g).2 (dvd_mul_right g c)
  have hMbot : M ≠ ⊥ := by
    intro hb
    have hgM := hJM hgJ
    rw [hb, Ideal.mem_bot] at hgM
    exact hg hgM
  obtain ⟨s, hsP, hs⟩ := h ⟨M, hM.isPrime, hMbot⟩ (hJM hgJ)
  exact hsP (hJM ((hJ s).2 hs))

theorem coeff_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) (c : Fin (r + 1) → 𝓞 E)
    (hc : ModG S Λ g (∑ a, ((c a : 𝓞 E) : E) • frame F a)) (a : Fin (r + 1)) : (g : 𝓞 E) ∣ c a := by
  classical
  have hcoe : ∀ (o : 𝓞 E) (v : S.V), o • v = (o : E) • v := fun o v => by
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
  have horth : ∀ v : S.V, (∀ i, S.hT (F.fl.e i) v = 0) → v ∈ orth S (Xsp F) := by
    intro v hv
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT.flip v) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simp [hv i]
    simpa using hle hx
  have hz_o : F.fl.z ∈ orth S (Xsp F) := horth _ F.fl.z_orth
  have hf_o : ∀ j, frame F j ∈ orth S (Xsp F) := by
    intro j
    induction j using Fin.lastCases with
    | last => simpa [frame, FlagG.fvec] using hz_o
    | cast i => simpa [frame, FlagG.fvec] using horth _ (fun k => F.fl.e_iso k i)
  have heX : ∀ i, F.fl.e i ∈ Xsp F := fun i => by
    show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxdec : ∑ a, ((c a : 𝓞 E) : E) • frame F a =
      ∑ i : Fin r, ((c i.castSucc : 𝓞 E) : E) • F.fl.e i + ((c (Fin.last r) : 𝓞 E) : E) • F.fl.z := by
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec]
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg0
  have hgcoe : ((g : 𝓞 E) : E) = (g : E) := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast]
  have hgO : (g : 𝓞 E) ≠ 0 := fun h0 => hgE (by rw [← hgcoe, h0]; simp [RingOfIntegers.coe_eq_algebraMap])
  apply dvd_of_loc hgO
  intro P hgP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ := hc P hgP
  have hsP : s ∉ P.asIdeal := hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsx
  obtain ⟨l, hlΛ, hl⟩ := hsx
  have hlE : l = ((g : E)⁻¹ * (s : E)) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
    have hl' : (g : E) • l = (s : E) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
      rw [← hgcoe, ← hcoe, ← hcoe, hl]
    rw [mul_smul, ← hl', smul_smul, inv_mul_cancel₀ hgE, one_smul]
  have hlx : l = ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i +
      ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z := by
    rw [hlE, hxdec, smul_add, Finset.smul_sum]
    simp only [smul_smul]

  have hzL : ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z ∈ Lsub Λ F := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · refine Submodule.mem_sup.2 ⟨l, ?_, -(∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i), ?_, ?_⟩
      · refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
        show l ∈ orth S (Xsp F)
        rw [hlE]
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hf_o a))
      · show _ ∈ Xsp F
        exact neg_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i))
      · rw [hlx]
        abel
    · show _ ∈ orth S (Xsp F)
      exact Submodule.smul_mem _ _ hz_o
  obtain ⟨o, ho⟩ := hFC.2 _ hzL
  induction a using Fin.lastCases with
  | last =>
    refine ⟨s, hsP, o, RingOfIntegers.ext ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at ho ⊢
    rw [ho]
    field_simp
  | cast j =>
    obtain ⟨cc, -, hcc1, hloc⟩ := hFC.1 P
    have hcc : ∀ i, cc i = 1 := hcc1 hgP
    set y : S.V := ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i with hy
    have hyl : y = l - o • F.fl.z := by
      rw [hcoe, ho, hlx]
      abel
    have hyX : y ∈ XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hyl]
        exact Submodule.sub_mem _ hlΛ (Submodule.smul_mem _ _ hz)
      · show y ∈ Xsp F
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i)
    have hyloc : y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hyX⟩
    rw [hloc] at hyloc
    obtain ⟨s', hs', hs'y⟩ := hyloc
    have hs'P : s' ∉ P.asIdeal := hs'
    simp only [hcc, one_smul] at hs'y
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs'y
    have hsum : ∑ i : Fin r, ((w i : E) - (s' : E) * ((g : E)⁻¹ * (s : E) * (c i.castSucc : E))) • F.fl.e i = 0 := by
      have h1 : ∑ i : Fin r, ((w i : 𝓞 E) : E) • F.fl.e i = (s' : E) • y := by
        rw [← hcoe, ← hw]
        exact Finset.sum_congr rfl fun i _ => (hcoe _ _).symm
      simp only [sub_smul, Finset.sum_sub_distrib, h1, hy, Finset.smul_sum, smul_smul]
      exact sub_self _
    have hj := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum j
    refine ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs'P hsP, w j, RingOfIntegers.ext ?_⟩
    rw [sub_eq_zero] at hj
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at hj ⊢
    rw [hj]
    field_simp

theorem wit_sub_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) {ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h : AdmWit Λ g F F' ξ) (h' : AdmWit Λ g F F' ξ') (a b : Fin (r + 1)) : (g : 𝓞 E) ∣ (ξ - ξ') a b := by
  have hM : ModG S Λ g (∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c) := by
    have heq : ∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c =
        (frame F' b - frameAct (frame F) ξ' b) - (frame F' b - frameAct (frame F) ξ b) := by
      simp only [frameAct, Matrix.sub_apply, RingOfIntegers.coe_eq_algebraMap, map_sub, sub_smul,
        Finset.sum_sub_distrib]
      abel
    rw [heq]
    intro P hP
    exact sub_mem (h'.2.2 b P hP) (h.2.2 b P hP)
  exact coeff_dvd Λ hg0 F hz hFC (fun c => (ξ - ξ') c b) hM a

theorem witness_congr : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsRowLat D F0 Λ → Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F' → ∀ ξ ξ' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit Λ (gS D) (lf D F0) F' ξ → AdmWit Λ (gS D) (lf D F0) F' ξ' → ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) - (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))} := by
  intro D Z u u' F0 Λ F' hR _hPD ξ ξ' hξ hξ' p a b
  obtain ⟨-, hFH, -⟩ := hR
  obtain ⟨-, -, hL, hFC⟩ := hFH
  have hg0 : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hdiff : ∀ c d, ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ - ξ') c d :=
    fun c d => wit_sub_dvd Λ hg0 (lf D F0) F' hL.1 hFC hξ hξ' c d
  have hdet : IsUnit ξ'.det := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => hξ'.1 i j hji)]
    simp [hξ'.2.1]
  have hkey : ξ * ξ'⁻¹ - 1 = (ξ - ξ') * ξ'⁻¹ := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ hdet]
  have hdvd : ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ * ξ'⁻¹ - 1) a b := by
    rw [hkey, Matrix.mul_apply]
    exact Finset.dvd_sum fun c _ => (hdiff a c).mul_right _
  obtain ⟨y, hy⟩ := hdvd
  have hsub : (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) -
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
      ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) := by
    have h1 : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
        (D.s.atP p).ιE (((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) a b : 𝓞 D.host.E) :
          D.host.E) := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h, RingOfIntegers.coe_eq_algebraMap]
    have h2 : (ξ * ξ'⁻¹) a b = (ξ * ξ'⁻¹ - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))
        (𝓞 D.host.E)) a b := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [h1, h2, hy]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_natCast, add_sub_cancel_right]
  obtain ⟨-, -, -, hO, -, hsp⟩ := Z.agree p
  have hyO : (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O := by
    rw [hO, (D.s.atP p).O_def]
    exact IsIntegral.tower_top ((RingOfIntegers.isIntegral_coe y).map (D.s.atP p).ιE.toIntAlgHom)
  have hgO : ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O :=
    mul_mem (natCast_mem _ _) hyO
  rw [hsub]
  unfold Formalism.MainNotions.S.LocNG.theta
  revert hsp
  cases hM : (Z.M p).split with
  | none =>
    intro _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hgO⟩, ?_⟩
    simp [Subring.smul_def]
  | some gM =>
    cases hD : (D.s.atP p).split with
    | none =>
      intro h
      exact h.elim
    | some sg =>
      rintro ⟨-, hq⟩
      have hl := (D.s_split p).1 (by rw [hD]; rfl)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      have hθ : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gM.q : (D.s.atP p).Fp) =
          ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : (D.s.atP p).Ep) := by
        rw [hq, sg.q_eq, map_natCast]
      rw [hθ]
      rcases hl with hl | hl
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 1 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 0 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring

end GlobalTheory.WitCong
