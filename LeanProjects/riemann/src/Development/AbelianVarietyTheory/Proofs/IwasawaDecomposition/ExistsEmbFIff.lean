import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.RowTie

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)

theorem exists_embF_iff (φ : S.Cl → Fr emb σ n → ℂ) :
    (∃ x, S.embF emb σ lam h x = φ) ↔
      φ ∈ S.Fi emb σ lam ∧ ∀ c, ∃ v : Formalism.L2.DIV.VV K lam, φ c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨StepZero.embF_mem_Fi S emb σ lam h x, fun c => ⟨x.1 c, rfl⟩⟩
  · rintro ⟨hφ, hv⟩
    choose v hv using hv
    refine ⟨⟨v, fun c γ => ?_⟩, funext fun c => (hv c).symm⟩
    apply evV_injective emb (1 : Matrix (Fin n) (Fin n) E) lam σ (fr0 emb σ n)
    show evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam c.1 γ.1 (v c)) = _
    rw [S.evV_rho_eq_tr emb σ lam, ← hv c]
    exact (hφ c).2 γ

theorem mem_L_iff (x : (S.hlat emb lam h).V) : x ∈ (S.hlat emb lam h).L ↔
    ∀ c (w : HeightOneSpectrum (𝓞 K)), x.1 c ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  show (∀ c, x.1 c ∈ _) ↔ _
  refine forall_congr' fun c => ⟨fun h w => lc_le_locP w _ h, fun h => ?_⟩
  rw [← lc_iInf_locP (delAtr emb lam (S.Lsh c.1 (S.rep c)))]
  exact Submodule.mem_iInf _ |>.2 h

end Gen

section Gen2

variable {F E K ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] [Field K] [NumberField K]
  [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

omit [StarRing E] [NumberField K] [StarRing K] in

theorem mem_Fi_iff {σ' : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (L : StepLevel F E σ' J T f bad) {e : ι → E →+* ℂ} (he : e = embAt σ emb) {lam' : ι → DomWeight n} (hl : lam = lam')
    (y : S.Cl → UPts σ' J (FiniteAdeleRing (𝓞 F) F)) (hy : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls L))
    (st : ∀ c, S.Stab c →* UJ (σ' : E →+* E) J)
    (hr : ∀ c (γ : UJ (σ' : E →+* E) J), γ ∈ (st c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ L.U.map (MulAut.conj (y c).1).toMonoidHom)
    (hst : ∀ c s, (st c s).1 = S.gam c.1 s.1)
    (hc : ∀ c (s : S.Stab c) (κ : L.U), (y c).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (st c s).1 * (y c).1 * κ.1 →
      ((L.chi κ : ℂˣ) : ℂ) = σ ((S.chr c.1 s.1 : Kˣ) : K))
    (z : S.Cl → Fr emb σ n → ℂ) :
    z ∈ S.Fi emb σ lam ↔ (show S.Cl → Frames (gramC J e) → ℂ from z) ∈ FiC L e lam' y := by
  subst he hl
  refine Iff.trans ?_ (mem_FiC_iff L _ _ y hy _).symm
  refine forall_congr' fun c => and_congr Iff.rfl ⟨fun h γ hγ κ e zz zz' hz => ?_, fun H g => ?_⟩
  · obtain ⟨s, hs⟩ := (hr c ⟨γ, hγ⟩).2 ⟨κ.1⁻¹, inv_mem κ.2, by
      show (y c).1 * κ.1⁻¹ * (y c).1⁻¹ = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ
      rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
      exact e⟩
    have h1 : S.gam c.1 s.1 = γ := by rw [← hst, hs]
    have h2 := hc c s κ (by rw [hs]; exact e)
    revert zz zz'
    intro (zz : Fr emb σ n) (zz' : Fr emb σ n) hz
    have h4 : zz = frMul emb σ γ zz' := Subtype.ext (funext hz)
    have h3 : σ ((S.chr c.1 s.1 : Kˣ) : K) * z c (frMul emb σ (S.gam c.1 s.1)⁻¹ zz) = z c zz := congrFun (h s) zz
    have h5 : frMul emb σ γ⁻¹ zz = zz' := by rw [h4, ← frMul_mul, inv_mul_cancel, frMul_one]
    rw [h1, ← h2, h5] at h3
    exact h3.symm
  · obtain ⟨k, hk, e⟩ := (hr c (st c g)).1 ⟨g, rfl⟩
    have e' : (y c).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (st c g).1 * (y c).1 * (⟨k⁻¹, inv_mem hk⟩ : L.U).1 := by
      rw [← e]
      show _ = (y c).1 * k * (y c).1⁻¹ * (y c).1 * k⁻¹
      group
    funext yy
    have h3 := H _ (st c g).2 _ e' yy (frMul emb σ (st c g).1⁻¹ yy) fun τ => by
      have h2 : yy = frMul emb σ (st c g).1 (frMul emb σ (st c g).1⁻¹ yy) := by
        rw [← frMul_mul, mul_inv_cancel, frMul_one]
      exact congrFun (congrArg Subtype.val h2) τ
    rw [hc c g _ e', hst] at h3
    exact h3.symm

variable (h : (S.fam emb lam).Ok)

theorem rat_iff {G : ι → Matrix (Fin n) (Fin n) ℂ} {lam₀ : ι → DomWeight n} (h0 : Formalism.L2.DIV.VV K lam = Formalism.L2.DIV.VV K lam₀)
    {sh : ι → ℤ} (hsh : sh = shiftOf lam) (z : S.Cl → Fr emb σ n → ℂ) :
    (∃ x, S.embF emb σ lam h x = z) ↔ z ∈ S.Fi emb σ lam ∧
      ∀ c, ∃ P ∈ RatSpanG σ lam₀, (show Frames G → ℂ from z c) = fnOf G sh 1 P := by
  subst hsh
  rw [exists_embF_iff]
  refine and_congr_right fun _ => forall_congr' fun c => ⟨?_, ?_⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, (mem_RatSpanG_iff σ lam₀ _).2 ⟨v.1, h0 ▸ v.2, rfl⟩, hv⟩
  · rintro ⟨P, hP, hv⟩
    obtain ⟨v, h1, rfl⟩ := (mem_RatSpanG_iff σ lam₀ _).1 hP
    exact ⟨⟨v, h0 ▸ h1⟩, hv⟩

theorem lat_iff (hS : S.Ok) {G : ι → Matrix (Fin n) (Fin n) ℂ} {sh : ι → ℤ} (hsh : sh = shiftOf lam) {e : ι → E →+* ℂ}
    (he : e = embAt σ emb) {P : Type} (pl : P ≃ HeightOneSpectrum (𝓞 K)) (rc : P → ℕ) (hrc : ∀ w, (rc w).Prime)
    (hm : ∀ w, ((rc w : ℕ) : 𝓞 K) ∈ (pl w).asIdeal) (Sp : P → AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (hSp : ∀ w Q, Q ∈ Sp w ↔ ∃ z₀ ∈ Formalism.HermitianLatticesTheory.localization₂ (pl w).asIdeal (delStd K lam), Q = MvPolynomial.map σ z₀)
    (lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, S.Lsh c.1 (S.rep c) = lat c) (x : (S.hlat emb lam h).V) :
    x ∈ (S.hlat emb lam h).L ↔ ∀ (w : P) (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (rc w) (lat c : Set _) B →
      ∃ Q ∈ Sp w, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G sh (Formalism.L2.Forms.atInf e (B⁻¹ : GL (Fin n) E).1) Q := by
  subst hsh he
  have hL : ∀ c, Submodule.IsLattice E (lat c) := fun c => hlat c ▸ hS.lsh_lat c.1 _
  have key : ∀ (w : P) (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (rc w) (lat c : Set _) B →
      (x.1 c ∈ Formalism.HermitianLatticesTheory.localization₂ (pl w).asIdeal (delAtr emb lam (lat c)) ↔
      ∃ Q ∈ Sp w, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G (shiftOf lam) (Formalism.L2.Forms.atInf (embAt σ emb) (B⁻¹ : GL (Fin n) E).1) Q) := by
    intro w c B hB
    refine (BwLat.mem_localization_delAtr_fn emb σ lam (pl w) (hL c) (fun _ => B) (fun τ => BwLat.isBasisAt_of_isLocBasis (hrc w) _
      ((bc_mem_below _ _ _).2 (by rw [map_natCast]; exact hm w)) hB) (x.1 c)).trans ⟨?_, ?_⟩
    · rintro ⟨z, hz, e⟩
      exact ⟨_, (hSp w _).2 ⟨z, hz, rfl⟩, e⟩
    · rintro ⟨Q, hQ, e⟩
      obtain ⟨z, hz, rfl⟩ := (hSp w Q).1 hQ
      exact ⟨z, hz, e⟩
  rw [mem_L_iff]
  simp only [hlat]
  refine ⟨fun H w c B hB => (key w c B hB).1 (H c _), fun H c w => ?_⟩
  obtain ⟨w, rfl⟩ := pl.surjective w
  haveI : Fact (rc w).Prime := ⟨hrc w⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (rc w) E _ (hL c).fg (hL c).span_eq_top
  exact (key w c B hB).2 (H w c B hB)

end Gen2

theorem petersson_apply {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
    {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (h : Q.Ok) (z z' : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) :
    letI := Q.clFin h
    Q.ipP emb σ h z z' = ∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ Q.sgT (z c) (z' c) := by
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

theorem rowPar_eq (B : Base) (u : B.Word) (τ : Tau B.R) : RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ) := by
  unfold RowPar.of
  rw [B.hcW_v, B.hcW_b, B.hcW_e]

theorem natW_shW {N : ℕ} (l : DomWeight N) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
  congr 1
  ring

theorem VV_shW {K ι : Type} [Field K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) (c : ℤ) :
    Formalism.L2.DIV.VV K (fun τ => GlobalTheory.Mem.Col2.shW (lam τ) c) = Formalism.L2.DIV.VV K lam := by
  unfold Formalism.L2.DIV.VV nablaSq
  simp only [natW_shW]

theorem delStd_shW {K ι : Type} [Field K] [NumberField K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) (c : ℤ) :
    delStd K (fun τ => GlobalTheory.Mem.Col2.shW (lam τ) c) = delStd K lam := by
  unfold delStd delSq
  simp only [natW_shW]

theorem mem_baseL_one (B : Base) (n : ℕ) (x : Fin n → B.host.E) : x ∈ TC.baseL B n 1 ↔ x ∈ stdLat B.host.E n := by
  rw [mem_stdLat]
  refine forall_congr' fun j => ⟨fun ⟨r, hr, _⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm, fun _ => one_dvd r⟩⟩

theorem sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    Formalism.L2.Forms.sgHC R P i = (RowPar.of P).sgHC i := by
  have hi := i.2
  have hN : R.N R.m = (R.k + R.m) + R.m * R.t := N_eq_blocks R R.m
  unfold Formalism.L2.Forms.sgHC RowPar.sgHC
  congr 1
  by_cases h1 : (i : ℕ) < R.k - 1
  · rw [dif_pos h1, dif_pos h1]
    rfl
  · rw [dif_neg h1, dif_neg h1]
    have h2 : ((i : ℕ) - (R.k - 1)) / (R.t + 1) < R.m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      have := R.two_le_m
      have e : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
      have e' : R.m * R.t.succ = R.m * (R.t + 1) := rfl
      omega
    rw [dif_pos h2]
    split_ifs with h3
    · simp [RowPar.bAt, h2]
      rfl
    · simp [RowPar.eAt, h2]
      rfl

end GlobalTheory.Mem.Col2.RowTie

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.Col2.RowTie

set_option maxHeartbeats 1000000 in

theorem clsP_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ u : B.Word, ∃ (KP : ClsPTied (D := (I.rec7 l Z)) u) (W : ValPTied u KP),
      I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) ∧
      NormPTie W ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → W.eW z c s = z c s' := by
  intro B X I hI hP l Z u
  have hgP : gramP (I.rec7 l Z) = 1 := (spaces_in_coordinates I hI hP l Z).2.1
  have hQ : I.Q I.mu0 = ∅ := by
    show QE I.sel ((I.tup I.mu0 : Tup B.fields.F B.fields.E B.fields.K I.S) : Chr B.fields.F B.fields.E B.fields.K) = ∅
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact ciQE_one I.sel
  have hbad : badG (I.rec7 l Z) = plUnder B.host.F (B.primes X).vGs := by
    ext v
    exact (plUnder_vGs B.sp.cm (BasePrimes.primes_ok B X).1 v).symm
  obtain ⟨L, R, hLb, hpt, hlev, hchr, hst, hstc⟩ := exists_cls (X := B.fields) B.sp.cm (rowTyG I.Ch I.Ps)
    (levQX B.R I.sel (I.tup I.mu0)) (fun _ => True) B.embLL hQ (levOk_base B X).split B.R.f (gramP (I.rec7 l Z)) hgP
    (badG (I.rec7 l Z)) hbad
  let KP : ClsPTied (D := I.rec7 l Z) u :=
    { lev := L
      y := R.y
      y_bij := R.y_bij
      lat := fun c => ((I.stX I.mu0).rep c).1.1.deco.1.N
      y_lat := R.y_lat
      lat_fin := fun c => (Module.Finite.iff_fg (R := 𝓞 (I.rec7 l Z).host.E)
        (M := Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).2 ((I.stX I.mu0).rep c).1.1.deco.2.lat.fg
      stabI := R.stabI
      stabI_inj := R.stabI_inj
      stabI_range := fun c γ => R.stabI_range c γ.1 γ.2 }

  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u I.mu0).sgT = Formalism.L2.Forms.sgT (D := I.rec7 l Z) u := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hF : FOk B.fields.emb B.embLL := (base_fields_primes_ok B X).2.2.2.1
  have hS : (I.stX I.mu0).Ok := (l.per u I.mu0).step
  have hsh : shiftOf (Formalism.L2.Forms.sgT (D := I.rec7 l Z) u) = shiftOf (I.perIn u I.mu0).sgT := congrArg shiftOf hsg.symm
  have hnf : nfAll (I.perIn u I.mu0).sgT = nfAll B.wts.sgW := MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have hG : ∀ (e : Tau B.R → B.host.E →+* ℂ) τ, gramC (gramP (I.rec7 l Z)) e τ = 1 := fun e τ => by
    rw [hgP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  letI : Fintype (I.stX I.mu0).Cl := (I.perIn u I.mu0).clFin (l.per u I.mu0)
  let W : ValPTied (D := I.rec7 l Z) u KP :=
    { sg := fun τ i => by
        have h2 := (sgHC_eq (B.hcW u τ) i).trans (congrArg (fun P => RowPar.sgHC P i) (rowPar_eq B u τ))
        exact (RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)
      eW := LinearEquiv.refl ℂ ((I.stX I.mu0).Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m - 1) → ℂ)
      ptC := fun z => mem_Fi_iff (I.stX I.mu0) B.fields.emb B.embLL (I.perIn u I.mu0).sgT L hemb hsg R.y R.y_bij R.stabI
        (fun c γ => R.stabI_range c γ.1 γ.2) hst hstc z
      ipP := fun o ho z z' P Q _ _ hz hz' => by
        have h1 := petersson_apply (I.perIn u I.mu0) B.fields.emb B.embLL (l.per u I.mu0) z z'
        refine h1.trans (Finset.sum_congr rfl fun c _ => congrArg _ ?_)
        have h2 := MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u I.mu0).sgT hnf hsh (hG _) (fun y => y) (fun _ => rfl)
          o ho (P c) (Q c)
        exact (congrArg₂ (fun a b => ipVal B.fields.emb B.embLL (I.perIn u I.mu0).sgT a b) (hz c) (hz' c)).trans h2
      rat := fun z => rat_iff (I.stX I.mu0) B.fields.emb B.embLL (I.perIn u I.mu0).sgT (l.fmL u I.mu0).famP
        (VV_shW B.wts.sgW _) hsh z
      lat := fun x => lat_iff (I.stX I.mu0) B.fields.emb B.embLL (I.perIn u I.mu0).sgT (l.fmL u I.mu0).famP hS hsh hemb
        (I.rec7 l Z).plEq (I.rec7 l Z).what₂.places.resChar (I.rec7 l Z).what₂.places.resChar_prime
        (GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z)) (fun w => IntSpan (I.rec7 l Z) w B.wts.sgW)
        (fun w Q => by
          have h := GlobalTheory.LvT.Built.ValLat.mem_closure_iff B.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
            ((I.rec7 l Z).val_nonneg_iff w) B.wts.sgW Q
          rw [← delStd_shW B.wts.sgW (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))] at h
          exact h)
        _ (fun c => RowTie.Lsh_empty _) x }
  refine ⟨KP, W, ⟨fun x => (hLb x).trans (mem_baseL_one B _ x).symm, fun _ => rfl, hpt, hlev, hchr, hst⟩, ?_, ?_⟩
  · intro s x Pc hPc o ho
    refine (MetricTie.norm_step B.fields.emb B.embLL (I.perIn u I.mu0).sgT (I.stX I.mu0) hF hS (l.fmL u I.mu0).famP hnf hsh (hG _)
      (fun y => y) (fun _ => rfl) s x Pc (fun c z => congrFun (hPc c) z) o ho).trans (Finset.sum_congr rfl fun c _ => ?_)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rfl
  · intro z c s s' h
    exact congrArg (z c) (Subtype.ext h.symm)

end GlobalTheory.Mem.Col2.TC

end
