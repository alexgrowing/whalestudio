import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedDatum

variable {D : D7}

theorem two_mul_half : (2 : AE D) * incA D (2⁻¹ : D.host.E) = 1 := by
  rw [← map_ofNat (incA D) 2, ← RingHom.map_mul, mul_inv_cancel₀ two_ne_zero, RingHom.map_one]

theorem symplOH_two (V W : HSp D) (x c : WO V W) : symplOH V W x (2 • c) = symplO V W x c := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [symplOH, two_nsmul, GlobalTheory.LatVac.symplO_add_right]
  linear_combination (symplO V W x c) * h2

theorem core (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L₁ L' : AddSubgroup (WO V W))
    (hI : ∀ w : AE D, finPart D w ∈ intAE D → ∀ x ∈ L₁, w • x ∈ L₁)
    (hψ : ∀ x ∈ L', ∀ y ∈ L', ψ (symplO V W x y) = 1)
    (e : AE D) (hee : e * e = e) (hec : e * cA D e = 0)
    (he : ∀ x ∈ L₁, e • x ∈ L') (hce : ∀ x ∈ L₁, cA D e • x ∈ L')
    (N k₀ M : ℕ) (hN : ∀ x ∈ L₁, N • x ∈ L') (hk : ∀ x ∈ L₁, k₀ • x ∈ L') (hkM : Nat.Coprime k₀ M) (hM : Odd M)
    (hMN : M ∣ N) (h2 : finPart D (e * incA D (2⁻¹ : D.host.E)) ∈ intAE D)
    (u X : WO V W) (h1 : u - X ∈ L₁) (hoff : (1 - e) • X ∈ L₁) (hMX : M • X ∈ L₁)
    (j : ℕ) (w : WO V W) (hw : w ∈ L₁) (hj : M ^ j • u = (2 * N) • w)
    (s : D.host.E) (hs : s ≠ 0) (hs' : finPart D (cA D e * incA D s⁻¹) ∈ intAE D) (w' : WO V W) (hw' : w' ∈ L₁)
    (hsu : incA D s • u = (2 * N) • w') :
    ∃ c ∈ L', u = e • X + 2 • c ∧ ψ (symplOH V W (e • X) (2 • c)) = 1 := by
  have ht := two_mul_half (D := D)
  generalize incA D (2⁻¹ : D.host.E) = t at ht h2
  have hd : u - e • X ∈ L₁ := by
    have : u - e • X = (u - X) + (1 - e) • X := by rw [sub_smul, one_smul]; abel
    rw [this]; exact add_mem h1 hoff
  have htwo : ∀ y : WO V W, 2 • t • y = y := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, Nat.cast_ofNat, ht, one_smul]
  have htwo' : ∀ y : WO V W, t • (2 * N) • y = N • y := fun y => by
    rw [mul_nsmul', smul_comm t 2, htwo]
  refine ⟨t • (u - e • X), ?_, by rw [htwo]; abel, ?_⟩
  · have a1 : (2 * k₀) • t • (u - e • X) ∈ L' := by
      rw [mul_nsmul, htwo]; exact hk _ hd
    have a2 : M ^ j • t • (u - e • X) ∈ L' := by
      have b1 : M ^ j • X ∈ L₁ := by
        have : M ^ j • X = (2 * N) • w - M ^ j • (u - X) := by rw [← hj, smul_sub]; abel
        rw [this]; exact sub_mem (nsmul_mem hw _) (nsmul_mem h1 _)
      have : M ^ j • t • (u - e • X) = N • w - e • (e * t) • M ^ j • X := by
        rw [← htwo', ← hj, smul_smul e, ← mul_assoc, hee, smul_comm (M ^ j) t, smul_sub, smul_sub, smul_comm (M ^ j) e,
          smul_smul t e, mul_comm t e]
      rw [this]
      exact sub_mem (hN _ hw) (he _ (hI _ h2 _ b1))
    have hc : IsCoprime ((2 * k₀ : ℕ) : ℤ) ((M ^ j : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Coprime.mul_left (Nat.coprime_two_left.2 hM) hkM).pow_right j)
    obtain ⟨a, b, hab⟩ := hc
    have := add_mem (zsmul_mem a1 a) (zsmul_mem a2 b)
    rwa [← natCast_zsmul, ← natCast_zsmul _ (M ^ j), smul_smul a, smul_smul b, ← add_smul, hab, one_smul] at this
  · obtain ⟨n, rfl⟩ := hMN
    have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
    have hss : incA D s⁻¹ * incA D s = 1 := by rw [← RingHom.map_mul, inv_mul_cancel₀ hs, RingHom.map_one]
    have hu : t • u = incA D s⁻¹ • (M * n) • w' := by
      rw [← htwo', ← hsu, smul_comm _ t, smul_smul _ (incA D s), hss, one_smul]
    have key : cA D e • t • (u - e • X) = (M : AE D) • n • cA D e • (cA D e * incA D s⁻¹) • w' := by
      rw [smul_sub, smul_sub, smul_comm t e, smul_smul _ e, mul_comm _ e, hec, zero_smul, sub_zero, hu,
        smul_smul (cA D e) (cA D e * _), ← mul_assoc, hcc, Nat.cast_smul_eq_nsmul, ← mul_nsmul', smul_smul,
        smul_comm (M * n)]
    have e1 : symplO V W (e • X) (t • (u - e • X)) =
        symplO V W (e • M • X) (n • cA D e • (cA D e * incA D s⁻¹) • w') := by
      have hM' : cA D (M : AE D) = M := map_natCast _ _
      have q1 := GlobalTheory.PlaceModel.symplO_smul V W e (e • X) (t • (u - e • X))
      have q2 := GlobalTheory.PlaceModel.symplO_smul V W (M : AE D) (e • X) (n • cA D e • (cA D e * incA D s⁻¹) • w')
      rw [smul_smul e e, hee, key] at q1
      rw [hM', Nat.cast_smul_eq_nsmul, smul_comm M e] at q2
      exact q1.trans q2.symm
    rw [symplOH_two, e1]
    exact hψ _ (he _ hMX) _ (nsmul_mem (hce _ (hI _ hs' _ hw')) _)

theorem idem_div_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (s : 𝓞 D.host.E)
    (hs : ∀ PP ∈ P, s ∉ PP.asIdeal) : finPart D (e * incA D (s : D.host.E)⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  by_contra h
  exact hs PP hPP (((hes PP hPP).2 s fun h0 => hs PP hPP (h0 ▸ zero_mem _)).2 h)

theorem nsmul_mem_latO (V W : HSp D) (LV LV' : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (n : ℕ)
    (h : ∀ s ∈ LV, n • s ∈ LV') (x : WO V W) (hx : x ∈ latO V W LV LW fun _ => True) :
    n • x ∈ latO V W LV' LW fun _ => True := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, _, h s hs, t, ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, star_nsmul, smul_mul_assoc, ← Finset.smul_sum,
      mul_smul_comm]
    rw [← Nat.cast_smul_eq_nsmul D.host.F, ← Nat.cast_smul_eq_nsmul D.host.F, TensorProduct.tmul_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem nsmul_std {m : ℕ} (Λ L : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (hΛ : ∀ v, v ∈ Λ ↔ (fun j => star (v j)) ∈ L) (n : ℕ)
    (h : Ideal.span {(n : 𝓞 D.host.E)} • Formalism.L2.Pj.stdLat D.host.E m ≤ Λ) :
    ∀ s ∈ (Formalism.L2.Pj.stdLat D.host.E m : Set (Fin m → D.host.E)), n • s ∈ (L : Set (Fin m → D.host.E)) := by
  intro s hs
  have h1 : (fun j => star (s j)) ∈ Formalism.L2.Pj.stdLat D.host.E m := by
    intro j hj
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hs j hj)
    refine Submodule.mem_one.2 ⟨Formalism.L2.Pj.barE D o, ?_⟩
    change ((Formalism.L2.Pj.barE D o : 𝓞 D.host.E) : D.host.E) = star (s j)
    rw [Formalism.L2.Pj.barE_eq_star, ← ho]
  have h2 := (hΛ _).1 (h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1))
  rw [Nat.cast_smul_eq_nsmul] at h2
  simp only [Pi.smul_apply, star_nsmul, star_star] at h2
  exact h2

theorem mulVec_finVec_mem (W : HSp D) (k g : GA D W) (v : Fin W.rank → D.host.E) (hv : v ∈ latG W g) :
    (finHom W k).1 *ᵥ finVec W v ∈ latGHat W (k * g) := by
  have hadd : ∀ x y, finVec W (x + y) = finVec W x + finVec W y := fun x y =>
    funext fun i => TensorProduct.tmul_add _ _ _
  have hzero : finVec W 0 = 0 := funext fun i => TensorProduct.tmul_zero _ _
  have key : ∀ c : 𝓞 D.host.E, (finHom W k).1 *ᵥ finVec W (c • v) ∈ latGHat W (k * g) := by
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, v, ⟨z, hz, hv⟩, rfl⟩ := hw
      intro c
      refine AddSubgroup.subset_closure ⟨(c : D.host.E) * a,
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha, _, ⟨z, hz, rfl⟩, ?_⟩
      have e1 : finVec W (c • a • v) =
          ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * a)) • finVec W v := by
        funext i
        change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * (a * v i)) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] v i)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
      rw [e1, Matrix.mulVec_smul, ← hv, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
      rfl
    | zero => intro c; rw [smul_zero, hzero, Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro c; rw [smul_add, hadd, Matrix.mulVec_add]; exact add_mem (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  have := key 1
  rwa [one_smul] at this

theorem finVec_mem (W : HSp D) (k : GA D W) (v : Fin W.rank → D.host.E) (hv : v ∈ latG W k) :
    finVec W v ∈ latGHat W k := by
  have := mulVec_finVec_mem W 1 k v hv
  rwa [map_one, Units.val_one, Matrix.one_mulVec, one_mul] at this

theorem smul_mt_inv (V : HSp D) (h : GA D V) (e' f : AE D) (hh : SuppAt e' V h) (hf : f * (e' + cA D e') = 0) :
    f • Formalism.L2.Theta.mt V h⁻¹ = f • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h1 : f • Formalism.L2.Theta.mt V h = f • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    rw [← sub_eq_zero, ← smul_sub]
    ext i j
    rw [Matrix.smul_apply, ← hh i j, smul_eq_mul, ← mul_assoc, hf, zero_mul, Matrix.zero_apply]
  have h2 := congrArg (· * Formalism.L2.Theta.mt V h⁻¹) h1
  simp only [Matrix.smul_mul, Matrix.one_mul] at h2
  rw [← h2, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]

theorem actO_smul (V W : HSp D) (h : GA D V) (k : GA D W) (f : AE D)
    (hf : f • Formalism.L2.Theta.mt V h⁻¹ = f • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) (x : WO V W) :
    actO V W h k (f • x) = f • (Formalism.L2.Theta.mt W k * x) := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_smul, hf, Matrix.mul_smul, Matrix.mul_one]

theorem actO_two (V W : HSp D) (h : GA D V) (k : GA D W) (x : WO V W) :
    actO V W h k (2 • x) = 2 • actO V W h k x := by
  simp only [actO, two_nsmul, Matrix.mul_add, Matrix.add_mul]

theorem infPart_moved (V W : HSp D) (k : GA D W) (ρ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    (Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ).map (infPart D) = 0 := by
  have : (GlobalTheory.LatVac.finTens (D := D) 1 ρ).map (infPart D) = 0 := by
    ext a b; exact GlobalTheory.LatVac.infPart_pair _ _
  rw [Matrix.map_mul, this, Matrix.mul_zero]

theorem finPart_moved (V W : HSp D) (k : GA D W) (ρ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (b : Fin V.rank) :
    (fun a => finPart D ((Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ) a b)) =
      (finHom W k).1 *ᵥ finVec W (fun a => ρ a b) := by
  funext a
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => RingHom.map_mul _ _ _

theorem smul_moved (V W : HSp D) (k : GA D W) (ρ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (s : D.host.E) :
    incA D s • (Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ) =
      Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 (s • ρ) := by
  rw [← Matrix.mul_smul]
  congr 1
  ext a b
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ρ a b) = _ ⊗ₜ[D.host.F] (s * ρ a b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_finTens {m n : ℕ} (ρ : Matrix (Fin m) (Fin n) D.host.E) (s : D.host.E) :
    incA D s • GlobalTheory.LatVac.finTens (D := D) 1 ρ = GlobalTheory.LatVac.finTens (D := D) 1 (s • ρ) := by
  ext a b
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ρ a b) = _ ⊗ₜ[D.host.F] (s * ρ a b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem incA_nat {m n : ℕ} (c : ℕ) (x : Mx D m n) : incA D (c : D.host.E) • x = c • x := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem infPart_finTens {m n : ℕ} (ρ : Matrix (Fin m) (Fin n) D.host.E) :
    (GlobalTheory.LatVac.finTens (D := D) 1 ρ).map (infPart D) = 0 := by
  ext a b; exact GlobalTheory.LatVac.infPart_pair _ _

theorem sub_sep_mem {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Geo.Tor.Level H) (q : LevQ Dw l) (a : Dw.La)
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) (hq : Submodule.Quotient.mk a = q) :
    ∃ z : Dw.La, a - cSep l • levRep q = l.M • z := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  have hc : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
    unfold cSep; rw [dif_pos hex]; exact hex.choose_spec
  have h1 : a - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
    (Submodule.Quotient.eq _).1 (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)).symm)
  have hp : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 D.host.E)} := l.prod
  have h2 : cSep l • (a - levRep q) - (cSep l - 1) • a ∈
      Ideal.span {(l.M : 𝓞 D.host.E)} • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
    rw [← hp]
    refine sub_mem ?_ ?_
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hc.1 h1
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hc.2 ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨z, -, hz⟩ := h2
  refine ⟨z, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), hz, smul_sub, sub_smul, one_smul]
  abel

theorem exists_unit_conj {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) {e : AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (hP : ∀ PP ∈ P, l.Mb ≤ PP.asIdeal) (j : ℕ) :
    ∃ s ∈ l.Mb ^ (j + 1), (s : D.host.E) ≠ 0 ∧ finPart D (cA D e * incA D (s : D.host.E)⁻¹) ∈ intAE D := by
  have hco : IsCoprime (l.Mb ^ (j + 1)) (Mfr l) := (Ideal.isCoprime_iff_sup_eq.2 l.coprime).pow_left
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 hco
  have hstar : ∀ a : 𝓞 D.host.E, ((H.bar a : 𝓞 D.host.E) : D.host.E) = star (a : D.host.E) := fun a => H.bar_eq a
  have hbb : ∀ a : 𝓞 D.host.E, H.bar (H.bar a) = a := fun a =>
    RingOfIntegers.coe_injective (by
      change ((H.bar (H.bar a) : 𝓞 D.host.E) : D.host.E) = (a : D.host.E)
      rw [hstar, hstar, star_star])
  have hy' : H.bar y ∈ l.Mb := by
    obtain ⟨m, hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) H.bar.surjective).1 hy
    change H.bar (H.bar m) ∈ _
    rwa [hbb]
  have hM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := by
    rw [show l.Mb * Mfr l = _ from l.prod]; exact Ideal.mem_span_singleton_self _
  by_cases h0 : x = 0
  · refine ⟨l.M ^ (j + 1), Ideal.pow_mem_pow (Ideal.mul_le_left hM) _, ?_, ?_⟩
    · have : l.M ≠ 0 := by have := l.three_le; omega
      exact_mod_cast pow_ne_zero _ this
    · have hP0 : ∀ PP, PP ∉ P := fun PP hPP => by
        rw [h0, zero_add] at hxy
        rw [hxy, map_one] at hy'
        exact PP.isPrime.one_notMem (hP PP hPP hy')
      obtain ⟨⟨es, -, rfl⟩, -⟩ := he
      rw [Finset.sum_eq_zero fun PP hPP => absurd hPP (hP0 PP), RingHom.map_zero, zero_mul, RingHom.map_zero]
      exact zero_mem _
  refine ⟨x, hx, fun h => h0 (RingOfIntegers.coe_injective (h.trans (map_zero _).symm)), ?_⟩
  have := GlobalTheory.MovedIdem.finPart_conj_mem (idem_div_mem he (H.bar x) fun PP hPP hm => by
    have := add_mem hm (hP PP hPP hy')
    rw [← map_add, hxy, map_one] at this
    exact PP.isPrime.one_notMem this)
  rwa [hstar, star_inv₀, star_star] at this

theorem natCast_mem_Mb {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
  have hM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := by
    rw [show l.Mb * Mfr l = _ from l.prod]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mul_le_left hM

theorem step (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (V W : HSp D) (hV : V.gram = 1) {r : ℕ}
    (hr : W.rank = r) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (a1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V)
    (a2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W) (a3 : IsSelfDualC V ΛV) (a4 : IsSelfDualC W ΛW)
    (a5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (hι : LatEmb W ι) (δ : ℤ)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, l.Mb ≤ PP.asIdeal ∧ (2 : 𝓞 D.host.E) ∉ PP.asIdeal) (bad N : ℕ) (h : GA D V) (k : GA D W)
    (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hbad : ∀ PP ∈ P, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hh : SplitOffBad V bad h)
    (hΛ : ∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (fin V h)) (hT : Λ.TrivAt l.M) (hL : Λ.LevOK N l.M)
    (hmk : MarkAd l W hr ι k mk) (Y : (Fin V.rank → LevQ Dw l) → Matrix (Fin V.rank) (Fin r) D.host.E)
    (hY : IsRoots l (latR hr (latG W k)) mk N Y) (q : Fin V.rank → LevQ Dw l)
    (hq : ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l • levRep (q b)) = l.M • z)
    (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W) (hγ : colsR hr γ = δ • Y q) (hu : IsFinOf V W γ u) :
    ∃ c₀ ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True,
      u = actO V W h k (Matrix.of fun a b => e * incA D ((δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))) +
        2 • actO V W h k c₀ ∧
      ψ (symplOH V W (actO V W h k
        (Matrix.of fun a b => e * incA D ((δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))))
        (2 • actO V W h k c₀)) = 1 := by
  subst hr
  have hR : ∀ v, v ∈ latR rfl (latG W k) → v ∈ latG W k := by
    rintro _ ⟨w, hw, rfl⟩; exact hw
  obtain ⟨m1, m2, m3, -, -, -⟩ := GlobalTheory.MovedLat.moved_lattices D V W ΛV ΛW a1 a2 a3 a4 h k
  obtain ⟨-, -, m4, -, m5, -⟩ := GlobalTheory.MovedLat.moved_lattices D V W ΛV ΛW a1 a2 a3 a4 1 k
  rw [show fin V 1 = 1 from map_one _, m5, a5] at m4
  obtain ⟨-, e', P', he', hP', hs'⟩ := hh
  have horth := GlobalTheory.T.idempotentSum_conjSum_orthogonal_dvd D e e' P P' bad he he' hbad hP'
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec := he.2
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have f1 := smul_mt_inv V h e' e hs' (by linear_combination e * horth - (e' + cA D e') * (hee + hec))
  have f2 := smul_mt_inv V h e' (cA D e) hs' (by linear_combination cA D e * horth - (e' + cA D e') * (hcc + hec))
  have i1 : finPart D e ∈ intAE D := by
    have := idem_div_mem he 1 fun PP _ => PP.isPrime.one_notMem
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one] at this
  have i2 : finPart D (cA D e) ∈ intAE D := by
    rw [GlobalTheory.MovedIdem.finPart_cA]; exact GlobalTheory.MovedIdem.sigR_mem_intAE i1
  have hmove : ∀ f : AE D, finPart D f ∈ intAE D →
      f • Formalism.L2.Theta.mt V h⁻¹ = f • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      ∀ x ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True,
      f • x ∈ latO V W (Bridge.hLat V (fin V h) : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
    intro f hf hf' x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (m4 x).1 hx
    refine (m3 _).2 ⟨f • x₀, ?_, ?_⟩
    · rw [a5]; exact GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ f hf _ hx₀
    · rw [actO_smul V W h k f hf', actO, inv_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one]
  obtain ⟨k₀, hk₀, -, hk₁⟩ := hT
  obtain ⟨-, hMN, hN⟩ := hL
  have hM0 : (l.M : D.host.E) ≠ 0 := by
    have : l.M ≠ 0 := by have := l.three_le; omega
    exact_mod_cast this
  set ρ : Matrix (Fin W.rank) (Fin V.rank) D.host.E :=
    Matrix.of fun a b => (δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E) with hρ
  have hy : (Matrix.of fun a b => e * incA D ((δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) : WO V W) =
      e • GlobalTheory.LatVac.finTens 1 ρ := by
    refine GlobalTheory.AdTh.LatOf.eq_of_parts ?_ ?_ <;> ext a b
    · change infPart D (e * _) = infPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.PlaceDatum.infPart_idemSum he, zero_mul, zero_mul]
    · change finPart D (e * _) = finPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul]; rfl
  have hu' : u = GlobalTheory.LatVac.finTens 1 γ :=
    GlobalTheory.AdTh.LatOf.eq_of_parts (hu.1.trans (infPart_finTens γ).symm) hu.2
  have hγ' : ∀ a b, γ a b = (δ : D.host.E) * Y q b a := fun a b => by
    have := congrFun (congrFun hγ b) a
    rw [Matrix.smul_apply, zsmul_eq_mul] at this
    exact this
  have hιm : ∀ z, (finHom W k).1 *ᵥ finVec W (ι z) ∈ latGHat W k := fun z => by
    have := mulVec_finVec_mem W k 1 (ι z) (hι.2 ▸ LinearMap.mem_range_self ι z)
    rwa [mul_one] at this
  have hX : ∀ s : 𝓞 D.host.E, (∀ b, ∃ z : Dw.La, s • (cSep l • levRep (q b)) = l.M • z) →
      incA D (s : D.host.E) • (Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ) ∈
        latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
          (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
    intro s hs
    rw [smul_moved]
    refine GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns D V W hV k _ (infPart_moved V W k _) fun b => ?_
    obtain ⟨z, hz⟩ := hs b
    rw [finPart_moved]
    convert hιm (δ • z) using 3
    funext a
    have := congrFun (congrArg ι hz) a
    rw [map_smul, map_nsmul, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul] at this
    have t2 : (s : D.host.E) * ι (cSep l • levRep (q b)) a = l.M * ι z a := this
    rw [map_zsmul, Pi.smul_apply, zsmul_eq_mul, Matrix.smul_apply, smul_eq_mul, hρ, Matrix.of_apply]
    field_simp
    linear_combination (δ : D.host.E) * t2
  choose j hj using fun b => (hY q b).2
  have hU : ∀ s ∈ l.Mb ^ (∑ b, j b + 1), ∃ w ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True, incA D (s : D.host.E) • u = (2 * N) • w := by
    intro s hs
    choose v hv hv' using fun b => hj b s (Ideal.pow_le_pow_right
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans (Nat.le_succ _)) hs)
    refine ⟨GlobalTheory.LatVac.finTens 1 (Matrix.of fun a b => (δ • v b) a),
      GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns D V W hV k _ (infPart_finTens _) fun b =>
        finVec_mem W k _ (Submodule.smul_of_tower_mem _ δ (hR _ (hv b))), ?_⟩
    rw [hu', smul_finTens, ← incA_nat, smul_finTens]
    congr 1
    refine Matrix.ext fun a b => ?_
    have := congrFun (hv' b) a
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul] at this
    have t2 : (s : D.host.E) * Y q b a = ((2 * N : ℕ) : D.host.E) * v b a := this
    change (s : D.host.E) * γ a b = ((2 * N : ℕ) : D.host.E) * (δ • v b a)
    rw [hγ', zsmul_eq_mul, mul_left_comm, t2, mul_left_comm]
  have h1 : u - Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ ∈
      latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
    refine GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns D V W hV k _ ?_ fun b => ?_
    · rw [Matrix.map_sub _ (RingHom.map_sub _), hu.1, infPart_moved, sub_zero]
    obtain ⟨a, ha, haq, hYa⟩ := (hY q b).1
    obtain ⟨z, hz⟩ := sub_sep_mem l (q b) a ha haq
    obtain ⟨w, hw, hw'⟩ := hmk a ha
    have hm := zsmul_mem (add_mem (add_mem (finVec_mem W k _ (hR _ hYa)) hw) (hιm z)) δ
    let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
      AddMonoidHom.mk' (finVec W) fun x y => funext fun i => TensorProduct.tmul_add _ _ _
    have hfv : ∀ x, finVec W x = fv x := fun _ => rfl
    have e1 : (fun a => finPart D ((u - Formalism.L2.Theta.mt W k * GlobalTheory.LatVac.finTens (D := D) 1 ρ) a b)) =
        fv (fun a => γ a b) - (finHom W k).1 *ᵥ fv (fun a => ρ a b) := by
      rw [← hfv, ← hfv, ← finPart_moved, hu']
      funext a
      rw [Matrix.sub_apply, RingHom.map_sub]
      rfl
    rw [e1]
    convert hm using 1
    have hMu : IsUnit ((l.M : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) := by
      rw [← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E))]
      exact (IsUnit.mk0 _ hM0).map _
    apply hMu.smul_left_cancel.1
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    have g1 : l.M • (fun a => γ a b) = δ • l.M • Y q b := by
      funext a
      change l.M • γ a b = δ • l.M • Y q b a
      rw [hγ', smul_comm δ, zsmul_eq_mul]
    have g2 : l.M • (fun a => ρ a b) = δ • (ι a - l.M • ι z) := by
      rw [← map_nsmul, ← map_sub, ← hz, sub_sub_cancel]
      funext a
      simp only [Pi.smul_apply, hρ, Matrix.of_apply, nsmul_eq_mul, zsmul_eq_mul]
      field_simp
    have g3 : l.M • (Y q b - (l.M : D.host.E)⁻¹ • mk a) = l.M • Y q b - mk a := by
      rw [smul_sub, ← Nat.cast_smul_eq_nsmul D.host.E _ (_ • _), smul_smul, mul_inv_cancel₀ hM0, one_smul]
    have hw2 : l.M • w = fv (mk a) - (finHom W k).1 *ᵥ fv (ι a) := hw'.symm
    rw [smul_comm l.M δ, smul_add l.M, smul_add l.M, hw2, hfv, hfv, ← map_nsmul fv, g3, smul_sub, ← map_nsmul fv, g1,
      ← Matrix.mulVec_smul, ← map_nsmul fv, g2]
    simp only [map_zsmul, map_sub, map_nsmul, Matrix.mulVec_smul, Matrix.mulVec_sub]
    rw [← smul_sub δ]
    congr 1
    abel
  obtain ⟨w, hw, hw'⟩ := hU _ (Ideal.pow_mem_pow (natCast_mem_Mb l) _)
  obtain ⟨s, hs, hs0, hsi⟩ := exists_unit_conj l he (fun PP hPP => (hP PP hPP).1) (∑ b, j b)
  obtain ⟨w₂, hw₂, hw₂'⟩ := hU s hs
  have hMX := hX l.M fun b => ⟨_, Nat.cast_smul_eq_nsmul _ _ _⟩
  rw [show ((l.M : 𝓞 D.host.E) : D.host.E) = l.M from map_natCast (algebraMap _ _) _, incA_nat] at hMX
  rw [← Nat.cast_pow, show ∀ n : ℕ, ((n : 𝓞 D.host.E) : D.host.E) = n from map_natCast (algebraMap _ _), incA_nat] at hw'
  obtain ⟨c, hc, hc1, hc2⟩ := core ψ V W _ _ (GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _)
    (fun x hx y hy => GlobalTheory.LatVac.char_sympl_eq_one hψ m1 m2 hx hy) e hee hec (hmove e i1 f1) (hmove _ i2 f2) N k₀ l.M
    (nsmul_mem_latO V W _ _ _ N (nsmul_std Λ.La _ hΛ N (hN.trans inf_le_left)))
    (nsmul_mem_latO V W _ _ _ k₀ (nsmul_std Λ.La _ hΛ k₀ hk₁)) hk₀ l.odd hMN
    (idem_div_mem he 2 fun PP hPP => (hP PP hPP).2) u _ h1
    (GlobalTheory.T.one_sub_idempotent_smul_mem_lattice D V W _ _ e P he _ fun s hs => hX s (hq s hs)) hMX _ w hw hw' s hs0 hsi w₂ hw₂ hw₂'
  obtain ⟨c₀, hc₀, rfl⟩ := (m3 c).1 hc
  rw [hy, actO_smul V W h k e f1]
  exact ⟨c₀, hc₀, hc1, hc2⟩

theorem moved_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_first D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨hp, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.T.theta_pair_characters_at_level D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := (hR.thP.vP i t).1
  rw [hδ t l φ hφ hP e he, map_smul]
  by_cases hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨m, hm⟩ := D.host.two_dvd_QS
      rw [hm, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) =
      R.ωP i t (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.AdTh.MovedDatum
