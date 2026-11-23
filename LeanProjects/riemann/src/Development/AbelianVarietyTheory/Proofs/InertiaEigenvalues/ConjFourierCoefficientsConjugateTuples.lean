import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDatum

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem transfer {d d' : DeltaDat Xo c n} {cx : Rul d.Xo₂ d.c₂} (hd : d' = { d with cδ := cx })
    (P : ∀ N : Submodule (𝓞 E) Dw.La, ((Fin n → Dw.La ⧸ N) → c.F) → Prop) (φ' : (Fin n → LevQc Dw d'.l₂) → c.F)
    (hP : P (Mfr d'.l₂ • ⊤) φ') {Cl : Type} (w' : Cl → (Fin n → LevQ Dw d'.l₂) → c.F)
    (hw : ∀ k q, d'.eF (w' k q) = phiHat d'.c₂ (fun x => d'.eF (φ' x)) q) :
    ∃ (φ : (Fin n → LevQc Dw d.l₂) → c.F) (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F), P (Mfr d.l₂ • ⊤) φ ∧
      (∀ k, HEq (w k) (w' k)) ∧ ∀ k q, d.eF (w k q) = phiHat d.c₂ (fun x => d.eF (φ x)) q := by
  subst hd
  exact ⟨φ', w', hP, fun _ => HEq.rfl, hw⟩

theorem exists_dilation (d : DeltaDat Xo c n) (hM : l.M ∣ d.l₂.M) (τ : ℂ ≃+* ℂ) (ta : c.F ≃+* c.F)
    (hta : ∀ a : c.F, ((ta a : c.F) : ℂ) = τ (a : ℂ)) (hz : τ (zeta l.M) = zeta l.M) :
    ∃ a a' : ℕ, a * a' ≡ 1 [MOD d.l₂.M] ∧ a' ≡ 1 [MOD l.M] ∧
      ∀ (φ φ' : (Fin n → LevQc Dw d.l₂) → c.F) (w w' u : c.F) (q : Fin n → LevQ Dw d.l₂),
        d.eF w = phiHat d.c₂ (fun x => d.eF (φ x)) q → d.eF w' = phiHat d.c₂ (fun x => d.eF (φ' x)) q →
        (∀ x, ta (φ (a' • x)) = u * φ' x) → ta w = u * w' := by
  let t₂ : d.c₂.F ≃+* d.c₂.F := (d.eF.symm.toRingEquiv.trans ta).trans d.eF.toRingEquiv
  have ht₂ : ∀ x : c.F, t₂ (d.eF x) = d.eF (ta x) := fun x => congrArg (fun y => d.eF (ta y)) (d.eF.symm_apply_apply x)
  have hco : ∀ x : d.c₂.F, ((t₂ x : d.c₂.F) : ℂ) = τ (x : ℂ) := fun x => hta (d.eF.symm x)
  obtain ⟨a, a', ha, haa⟩ := exists_zetaM_pow d.c₂ t₂
  have h3 := l.three_le
  have h3' := d.l₂.three_le
  have h1 : a ≡ 1 [MOD l.M] := by
    obtain ⟨p, hp⟩ := hM
    haveI : NeZero l.M := ⟨by omega⟩
    have hζ : IsPrimitiveRoot (zeta d.l₂.M) d.l₂.M := Complex.isPrimitiveRoot_exp _ (by omega)
    have hζ0 : IsPrimitiveRoot (zeta l.M) l.M := Complex.isPrimitiveRoot_exp _ (by omega)
    have hζp : IsPrimitiveRoot (zeta d.l₂.M ^ p) l.M := hζ.pow (by omega) (hp.trans (mul_comm _ _))
    obtain ⟨m, -, hm⟩ := hζ0.eq_pow_of_pow_eq_one hζp.pow_eq_one
    have e1 : τ (zeta d.l₂.M) = zeta d.l₂.M ^ a := by
      have := congrArg (fun x : d.c₂.F => (x : ℂ)) ha
      simpa only [hco, SubmonoidClass.coe_pow, GlobalTheory.LevelPairing.zetaM_coe] using this
    have e2 : (zeta d.l₂.M ^ p) ^ a = (zeta d.l₂.M ^ p) ^ 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← e1, ← map_pow, ← hm, map_pow, hz, pow_one]
    have h0 : zeta d.l₂.M ^ p ≠ 0 := hζp.ne_zero (by omega)
    have e3 : (zeta d.l₂.M ^ p) ^ ((1 : ℤ) - a) = 1 := by
      rw [zpow_sub₀ h0, zpow_natCast, e2, zpow_one, pow_one, div_self h0]
    exact (Nat.modEq_iff_dvd).2 (by simpa using (hζp.zpow_eq_one_iff_dvd _).1 e3)
  refine ⟨a, a', haa, ?_, fun φ φ' w w' u q hw hw' h => d.eF.injective ?_⟩
  · have h2 : a * a' ≡ 1 * a' [MOD l.M] := h1.mul_right a'
    rw [one_mul] at h2
    exact h2.symm.trans (haa.of_dvd hM)
  · rw [← ht₂, hw, map_phiHat d.c₂ t₂ ha haa, map_mul, hw', ← phiHat_mul]
    congr 1
    funext x
    rw [ht₂, h, map_mul]

theorem level_mem {P : Ideal (𝓞 E)} (h : l.Mb ≤ P) : (l.M : 𝓞 E) ∈ P := by
  have h1 : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    rw [Mfr, l.prod]; exact Ideal.mem_span_singleton_self _
  exact h (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).1

theorem cast_eq_of_modEq {P : Ideal (𝓞 E)} {m a b : ℕ} (hm : (m : 𝓞 E) ∈ P) (h : a ≡ b [MOD m]) :
    (a : 𝓞 E ⧸ P) = (b : 𝓞 E ⧸ P) := by
  obtain ⟨k, hk⟩ := h.dvd
  have h0 : ((m : ℕ) : 𝓞 E ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hm
  have := congrArg (Int.cast : ℤ → 𝓞 E ⧸ P) hk
  push_cast at this
  rw [h0, zero_mul, sub_eq_zero] at this
  exact this.symm

end Gen

section Mat

variable {D : D7}

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) (h' : IsIdemSum e' P) : e' = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  refine Finset.sum_congr rfl fun PP hPP => ?_
  exact (((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 PP _ _ (Or.inl ⟨hes PP hPP, rfl⟩)).2.2.2.1 _ _
    (Or.inl ⟨hes' PP hPP, rfl⟩)).1

theorem uMat_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) (m : ℕ) :
    uMat S T βS βT e (fun b => m • X b) = m • uMat S T βS βT e X := by
  have h1 : (Matrix.of fun b a => D.sp.cm.sig ((m • X b) a)) = m • Matrix.of fun b a => D.sp.cm.sig (X b a) := by
    ext b a
    simp
  funext b a
  unfold uMat
  rw [h1, Matrix.mul_smul, Matrix.smul_mul]
  have h2 : ∀ N : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (m • N).map (eToEAf D) = m • N.map (eToEAf D) := fun N => by
    ext b a
    simp
  rw [h2, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.smul_apply, mul_smul_comm]
  rfl

theorem redM_nsmul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (m : ℕ) :
    redM PP (m • N) = (m : kP PP) • redM PP N := by
  funext i j
  have h : (m • N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := nsmul_mem (hN i j) m
  show redM PP (m • N) i j = (m : kP PP) * redM PP N i j
  unfold redM
  rw [dif_pos h, dif_pos (hN i j), ← nsmul_eq_mul]
  exact (resS D.host.F PP).toAddMonoidHom.map_nsmul m ⟨N i j, hN i j⟩

theorem topL_smul {κ : Type} [CommRing κ] {b a : ℕ} (k : ℕ) (c : κ) (y : Matrix (Fin b) (Fin a) κ) :
    topL k (c • y) = c • topL k y := by
  funext i j
  simp only [topL, Matrix.smul_apply]
  split_ifs <;> simp

theorem omegaK_smul {a b : ℕ} (Pg : Finset (Pl D.host.E)) (c : ∀ PP : Pl D.host.E, kP PP) (hc : ∀ PP ∈ Pg, c PP = 1)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaK Pg (fun PP => c PP • y PP) = omegaK Pg y := by
  unfold omegaK
  refine if_congr (forall₂_congr fun PP h => ?_) rfl rfl
  dsimp only
  rw [hc PP h, one_smul]

theorem map_omegaK (τ : ℂ ≃+* ℂ) {a b : ℕ} (Pg : Finset (Pl D.host.E))
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : τ (omegaK Pg y) = omegaK Pg y := by
  unfold omegaK
  split_ifs <;> simp

theorem map_omegaQ_smul (τ : ℂ ≃+* ℂ) {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (c : ∀ PP : Pl D.host.E, kP PP)
    (v : ∀ PP ∈ Q, (kP PP)ˣ) (hv : ∀ PP h, (v PP h : kP PP) * c PP = 1)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    τ (omegaQ Q r ξ (-1) (fun PP => c PP • y PP)) =
      (∏ PP ∈ Q.attach, ((ξ' PP.1 (v PP.1 PP.2 ^ r) : ℂˣ) : ℂ)) * omegaQ Q r ξ' (-1) y := by
  have hc : ∀ PP h, c PP = ((v PP h)⁻¹ : (kP PP)ˣ) := fun PP h => (Units.inv_eq_of_mul_eq_one_right (hv PP h)).symm
  have hdet : ∀ PP h, (topL r (c PP • y PP)).det = (((v PP h ^ r)⁻¹ : (kP PP)ˣ) : kP PP) * (topL r (y PP)).det := fun PP h => by
    rw [topL_smul, Matrix.det_smul, Fintype.card_fin, hc PP h, ← inv_pow, Units.val_pow_eq_pow_val]
  have hiff : (∀ PP ∈ Q, LowZero r (c PP • y PP) ∧ IsUnit (topL r (c PP • y PP)).det) ↔
      ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
    refine forall₂_congr fun PP h => and_congr ?_ ?_
    · refine forall₄_congr fun i j _ _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, hc PP h, Units.mul_right_eq_zero]
    · rw [hdet PP h, Units.isUnit_units_mul]
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos h, dif_pos (hiff.2 h), map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (hiff.2 h PP.1 PP.2).2.unit = (v PP.1 PP.2 ^ r)⁻¹ * (h PP.1 PP.2).2.unit :=
      Units.ext (by rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec]; exact hdet PP.1 PP.2)
    rw [map_zpow₀, ← hξ PP.1 PP.2, e, MonoidHom.map_mul, MonoidHom.map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      _root_.zpow_neg_one, _root_.zpow_neg_one, mul_inv, inv_inv]
  · rw [dif_neg h, dif_neg (mt hiff.1 h), map_zero, mul_zero]

theorem exists_idele_at {PP : Pl D.host.E} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e PP) (v : (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ∀ (χ : (AE D)ˣ →* Circle) (χH : Formalism.L2.Host.HChar D.host.E) (ξ : (kP PP)ˣ →* ℂˣ),
      ChrEq χ χH → IsRes χH PP ξ → ((χ s : Circle) : ℂ) = ((ξ v : ℂˣ) : ℂ) := by
  obtain ⟨⟨h1, h2, w, ε, hw, hs⟩, h3⟩ := he
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (v : kP PP)
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hx0 : (x : D.host.E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, map_zero] at hx
    exact v.ne_zero hx.symm
  refine ⟨(Formalism.L2.JoinChr.isUnit_locE h1 (Units.mk0 _ hx0)).unit, fun χ χH ξ hχ hξ => ?_⟩
  rw [hχ.2 PP e ⟨h1, ⟨w, ε, hw, Or.inl ⟨h2, hs⟩⟩, h3⟩ (Units.mk0 _ hx0) _ (IsUnit.unit_spec _),
    hξ x (Units.mk0 _ hx0) v rfl hx.symm]

theorem exists_idele (χ : (AE D)ˣ →* Circle) (χH : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq χ χH) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (hξ : ∀ PP ∈ Q, IsRes χH PP (ξ PP))
    (he : ∀ PP ∈ Q, ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP) (v : ∀ PP ∈ Q, (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ((χ s : Circle) : ℂ) = ∏ PP ∈ Q.attach, ((ξ PP.1 (v PP.1 PP.2) : ℂˣ) : ℂ) := by
  have key : ∀ PP : {x // x ∈ Q}, ∃ s : (AE D)ˣ, ((χ s : Circle) : ℂ) = ((ξ PP.1 (v PP.1 PP.2) : ℂˣ) : ℂ) := fun PP =>
    (he PP.1 PP.2).elim fun _ h => (exists_idele_at h (v PP.1 PP.2)).imp fun _ hs => hs χ χH _ hχ (hξ PP.1 PP.2)
  choose s hs using key
  refine ⟨∏ PP ∈ Q.attach, s PP, ?_⟩
  rw [map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun PP _ => hs PP)

end Mat

section Dat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1600000 in

theorem datum_conj (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ)
    (τ : ℂ ≃+* ℂ) {t t' : T0} (ht : ConjTup R τ t t') {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ φ' : (Fin (Vc D i).rank → La ⧸ N) → K') (h : PhiIs R i σ' t ι N φ) (h' : PhiIs R i σ' t' ι N φ') (a a' : ℕ)
    (hg : ∀ PP ∈ R.Pg, (a' : kP PP) = 1) (hq : ∀ PP ∈ R.Q t, (a : kP PP) * a' = 1) :
    ∃ s : (AE D)ˣ, ∀ x, τ (σ' (φ (a' • x))) = ((R.xi t' s : Circle) : ℂ) * σ' (φ' x) := by
  obtain ⟨e, he, h⟩ := h
  obtain ⟨e', he', h'⟩ := h'
  have hQ : R.Q t' = R.Q t := ht.1
  rw [hQ] at he' h'
  obtain rfl : e' = e := idemSum_unique (Vc D i) he he'
  have hid : ∀ PP ∈ R.Q t, ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP := fun PP hPP =>
    he.1.elim fun es hes => ⟨es PP, hes.1 PP (Finset.mem_union_right _ hPP)⟩
  have hres : ∀ PP ∈ R.Q t, IsRes (R.xiH t') PP (R.xiR t' PP) := fun PP hPP => hL.xiR t' PP (hQ ▸ hPP)
  have hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := fun PP hPP x => by
    obtain ⟨e₀, he₀⟩ := hid PP hPP
    obtain ⟨s, hs⟩ := exists_idele_at he₀ x
    rw [← hs _ _ _ (hL.xi t') (hres PP hPP), ← hs _ _ _ (hL.xi t) (hL.xiR t PP hPP)]
    exact ht.2 s
  let v : ∀ PP ∈ R.Q t, (kP PP)ˣ := fun PP hPP => Units.mkOfMulEqOne _ _ (hq PP hPP)
  obtain ⟨s, hs⟩ := exists_idele (R.xi t') (R.xiH t') (hL.xi t') (R.Q t) (R.xiR t') hres hid
    (fun PP hPP => v PP hPP ^ (Wc D i).rank)
  refine ⟨s, fun x => ?_⟩
  choose y hy using fun b => Submodule.Quotient.mk_surjective N (x b)
  obtain rfl : x = fun b => Submodule.Quotient.mk (y b) := funext fun b => (hy b).symm
  have e1 : (a' • fun b => (Submodule.Quotient.mk (y b) : La ⧸ N)) = fun b => Submodule.Quotient.mk (a' • y b) :=
    funext fun b => (map_nsmul N.mkQ a' (y b)).symm
  have e2 : (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e' fun b => ι (a' • y b))) =
      fun PP => (a' : kP PP) • redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e' fun b => ι (y b)) := by
    funext PP
    rw [← redM_nsmul PP (h y).1, ← uMat_nsmul]
    simp only [map_nsmul]
  rw [e1, (h fun b => a' • y b).2, (h' y).2, e2, map_mul, map_omegaK, omegaK_smul _ _ hg,
    map_omegaQ_smul τ _ _ _ _ hξ _ v hq, hs, mul_left_comm]

end Dat

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem conj_coeff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ) (w' : M.Cl' a → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (M.dδ a).l₂) → M.c'.F), (u : ℂ) = ((R.xi (tup b) s : Circle) : ℂ) ∧ (∀ k, HEq (w' k) (M.w b (e k))) ∧ ∀ k q, ta (M.w a k q) = u * w' k q := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore _ i Tp tup M hP τ ta hta hfix a b e hsame hconj
  obtain ⟨⟨cx, hcx⟩, -⟩ := hsame
  obtain ⟨φ', w', hφ', hw1, hw2⟩ := transfer hcx
    (fun N φ => PhiIs R i (inC M.c') (tup b) (iotaW T i) N φ) (M.φ b) (hP.tuple b).phi (M.w b) (hP.w b)
  have hLev := (hP.cov a).1
  have hz : τ (zeta T.Q.l.M) = zeta T.Q.l.M := by
    have := hfix.core (zetaM T.Q.c)
    rwa [GlobalTheory.LevelPairing.zetaM_coe] at this
  obtain ⟨m, m', hmm, hm', hdil⟩ := exists_dilation (M.dδ a) hLev.1.1 τ ta hta hz
  have hhalf := (hP.tuple a).half
  have hg : ∀ PP ∈ R.Pg, (m' : kP PP) = 1 := fun PP hPP => by
    have h1 : T.Q.l.Mb ≤ PP.asIdeal := hhalf.1.le.trans (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hPP))
    exact (cast_eq_of_modEq (level_mem h1) hm').trans Nat.cast_one
  have hq : ∀ PP ∈ R.Q (tup a), (m : kP PP) * m' = 1 := fun PP hPP => by
    have h1 : (M.dδ a).l₂.Mb ≤ PP.asIdeal := hLev.2.2.2.1.le.trans (Ideal.mul_le_right.trans (hhalf.2.1 PP hPP))
    exact (Nat.cast_mul m m').symm.trans ((cast_eq_of_modEq (level_mem h1) hmm).trans Nat.cast_one)
  obtain ⟨s, hs⟩ := datum_conj R hcore.lev i (inC M.c') τ hconj (iotaW T i) _ (M.φ a) φ' (hP.tuple a).phi hφ' m m' hg hq
  have hs' : ∀ x, ((ta (M.φ a (m' • x)) : M.c'.F) : ℂ) = ((R.xi (tup b) s : Circle) : ℂ) * ((φ' x : M.c'.F) : ℂ) :=
    fun x => (hta _).trans (hs x)
  have key : ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ x, ta (M.φ a (m' • x)) = u * φ' x := by
    by_cases h0 : ∀ x, φ' x = 0
    · refine ⟨1, 1, by simp, fun x => Subtype.ext ?_⟩
      rw [hs' x, h0 x]
      simp
    · obtain ⟨x₀, hx₀⟩ := not_forall.1 h0
      have hx₁ : ((φ' x₀ : M.c'.F) : ℂ) ≠ 0 := fun h => hx₀ (Subtype.ext h)
      have hu : ((ta (M.φ a (m' • x₀)) / φ' x₀ : M.c'.F) : ℂ) = ((R.xi (tup b) s : Circle) : ℂ) := by
        push_cast
        rw [hs' x₀, mul_div_cancel_right₀ _ hx₁]
      refine ⟨_, s, hu, fun x => Subtype.ext ?_⟩
      rw [hs' x, ← hu]
      rfl
  obtain ⟨u, s', hu, hus⟩ := key
  exact ⟨u, s', fun k => w' (e k), hu, fun k => hw1 (e k),
    fun k q => hdil (M.φ a) φ' _ _ u q (hP.w a k q) (hw2 (e k) q) hus⟩

end GlobalTheory.ConjDatum
