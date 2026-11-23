import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BasePoint

open GlobalTheory.AdjDatumNe in

theorem exists_point {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type)
    [∀ i, CommRing (k i)] (φ : ∀ i, O → k i) (crt : ∀ t : ∀ i, k i, ∃ c, ∀ i ∈ P, φ i c = t i) {n r : ℕ}
    (ρ : ∀ i, Fin r → La →+ k i) (hs : ∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) (J : Submodule O La)
    (hker : ∀ x, x ∈ J ↔ ∀ i ∈ P, ∀ a, ρ i a x = 0)
    (hon : ∀ t : ∀ i, Fin r → k i, ∃ x, ∀ i ∈ P, ∀ a, ρ i a x = t i a)
    (B B' : ∀ i, Matrix (Fin n) (Fin n) (k i)) (hB : ∀ i, B' i * B i = 1) (hrn : r ≤ n) :
    ∃ x1 : Fin n → La ⧸ J, Submodule.span O (Set.range x1) = ⊤ ∧ ∀ x : Fin n → La,
      (fun b => Submodule.Quotient.mk (x b)) = x1 ↔
        ∀ i ∈ P, B' i * (Matrix.of fun b a => ρ i a (x b)) = rectOne (k i) n r := by
  choose z hz using fun b : Fin n => hon fun i a => (B i * rectOne (k i) n r) b a
  have heq : ∀ x y : La, (Submodule.Quotient.mk x : La ⧸ J) = Submodule.Quotient.mk y ↔
      ∀ i ∈ P, ∀ a, ρ i a x = ρ i a y := fun x y => by
    rw [Submodule.Quotient.eq, hker]
    simp only [map_sub, sub_eq_zero]
  refine ⟨fun b => Submodule.Quotient.mk (z b), eq_top_iff.2 fun q _ => ?_, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose c hc using fun b : Fin n => crt fun i => ∑ a', ρ i a' x * B' i (Fin.castLE hrn a') b
    have : (Submodule.Quotient.mk x : La ⧸ J) = Submodule.Quotient.mk (∑ b, c b • z b) := by
      refine (heq _ _).2 fun i hi a => ?_
      rw [map_sum]
      simp only [hs, hc _ i hi, hz _ i hi, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum]
      have h1 : ∀ a', ∑ b, B' i (Fin.castLE hrn a') b * (B i * rectOne (k i) n r) b a = if a' = a then 1 else 0 := fun a' => by
        rw [← Matrix.mul_apply, ← Matrix.mul_assoc, hB, Matrix.one_mul]
        simp only [rectOne, Fin.ext_iff, Fin.val_castLE]
      simp [h1]
    rw [this]
    change (Submodule.mkQ J) _ ∈ _
    rw [map_sum]
    exact sum_mem fun b _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [funext_iff]
    simp only [heq]
    constructor
    · intro h i hi
      have : (Matrix.of fun b a => ρ i a (x b)) = B i * rectOne (k i) n r :=
        Matrix.ext fun b a => (h b i hi a).trans (hz b i hi a)
      rw [this, ← Matrix.mul_assoc, hB, Matrix.one_mul]
    · intro h b i hi a
      rw [hz b i hi a, ← h i hi, ← Matrix.mul_assoc, mul_eq_one_comm.1 (hB i), Matrix.one_mul]
      rfl

open GlobalTheory.AdjDatumNe Formalism.IndefR.Datum in
theorem low_top_iff {κ : Type} [Zero κ] [One κ] {n r : ℕ} (hrn : r ≤ n) (y : Matrix (Fin n) (Fin r) κ) :
    (LowZero r y ∧ topL r y = 1) ↔ y = rectOne κ n r := by
  constructor
  · rintro ⟨h1, h2⟩
    ext b a
    by_cases hb : b.val < r
    · have := congrFun (congrFun h2 ⟨b.val, hb⟩) a
      rw [topL, dif_pos ⟨b.2, a.2⟩, Matrix.one_apply] at this
      simpa only [rectOne, Fin.ext_iff] using this
    · rw [h1 b a (by omega) a.2, rectOne, if_neg (by omega)]
  · rintro rfl
    exact ⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hrn⟩

section Pairing

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.LevelDatum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem crt_places {E : Type} [Field E] [NumberField E] (P : Finset (Pl E)) (t : ∀ PP : Pl E, kP PP) :
    ∃ c : 𝓞 E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal c = t PP := by
  obtain ⟨c, hc⟩ := Ideal.pi_quotient_surjective (I := fun PP : P => PP.1.asIdeal)
    (fun x y hxy => HeightOneSpectrum.isCoprime_of_ne _ _ fun h => hxy (Subtype.ext h)) fun PP => t PP.1
  exact ⟨c, fun PP h => hc ⟨PP, h⟩⟩

variable {D : D7}

def pr (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

theorem exists_dual (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) : ∃ (n : ℕ) (s' : Fin n → Fin W.rank → D.host.E)
      (A : Matrix (Fin W.rank) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
      (B : Matrix (Fin n) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)),
      (∀ k, s' k ∈ Λ) ∧ A * B = 1 ∧ (∀ k a, (B k a : EAf D) = pr W β (s' k) a) ∧
      ∀ y ∈ Λ, ∃ c : Fin n → 𝓞 D.host.E, y = ∑ k, D.sp.cm.sig (c k : D.host.E) • s' k ∧
        ∀ k, eToEAf D (c k : D.host.E) = ∑ a, pr W β y a * A a k := by
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβ
  have fT : Formalism.L2.DIV.IsFrame β Λ := hβ.choose_spec.1
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D W Λ hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin W.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin W.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * W.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : W.gram * s₁ * s₂ᴴ = 1 := by
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [Matrix.mul_assoc]; exact e1)
  have i2 : IsIntM ((β⁻¹).val * s₁.map (eToEAf D)) := fun a k => by
    rw [hs₁]
    exact (fT _).1 (Submodule.subset_span ⟨_, (hs k).1, rfl⟩) a
  have i1 : ∀ k a, pr W β (s' k) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun k a =>
    GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ _ ((GlobalTheory.DatumFourier.mem_latG_one hβ _).2 (hs k).2) a
  have hpr : (Matrix.of fun k a => pr W β (s' k) a) = (s₂ᴴ * W.gram).map (eToEAf D) * β.val := by
    rw [hs₂]; rfl
  refine ⟨n, s', Matrix.of fun a k => ⟨_, i2 a k⟩, Matrix.of fun k a => ⟨_, i1 k a⟩, fun k => (hs k).2, ?_, fun _ _ => rfl, fun y hy => ?_⟩
  · have h : ((β⁻¹).val * s₁.map (eToEAf D)) * (Matrix.of fun k a => pr W β (s' k) a) = 1 := by
      rw [hpr, Matrix.mul_assoc, ← Matrix.mul_assoc (s₁.map _), ← Matrix.map_mul, e1,
        Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mul, Units.inv_mul]
    ext a a'
    have := congrFun (congrFun h a) a'
    rw [Matrix.mul_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum]
    refine this.trans ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · choose c hc using fun k => (hT.2 (s k)).1 (hs k).1 y hy
    have hc' : (fun k => (c k : D.host.E)) = star y ᵥ* (W.gram * s₁) := by
      funext k
      rw [hc, hs₁]
      simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc, Pi.star_apply, Matrix.of_apply]
    refine ⟨c, ?_, fun k => ?_⟩
    · have h : (fun k => (c k : D.host.E)) ᵥ* s₂ᴴ = star y := by
        rw [hc', Matrix.vecMul_vecMul, e2, Matrix.vecMul_one]
      funext a
      have := congrArg star (congrFun h a)
      rw [Pi.star_apply, star_star] at this
      rw [← this, hs₂, Finset.sum_apply]
      simp only [Matrix.vecMul, dotProduct, star_sum, star_mul', Matrix.conjTranspose_apply, star_star, Matrix.of_apply]
      rfl
    · have h1 : (fun a => pr W β y a) = (fun j => eToEAf D ((star y ᵥ* W.gram) j)) ᵥ* β.val := rfl
      change _ = ((fun a => pr W β y a) ᵥ* ((β⁻¹).val * s₁.map (eToEAf D))) k
      rw [h1, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, congrFun hc' k,
        ← Matrix.vecMul_vecMul]
      simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem pr_int {W : HSp D} {β : GL (Fin W.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hβ : IsSDFrame W β Λ 1) {y : Fin W.rank → D.host.E} (hy : y ∈ Λ) (a : Fin W.rank) :
    pr W β y a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ _ ((GlobalTheory.DatumFourier.mem_latG_one hβ _).2 hy) a

theorem smul_mem_latG {W : HSp D} {β : GL (Fin W.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hβ : IsSDFrame W β Λ 1) {y : Fin W.rank → D.host.E} (hy : y ∈ Λ) :
    ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) • y ∈ latG W 1 :=
  Submodule.subset_span ⟨_, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D, y,
    (GlobalTheory.DatumFourier.mem_latG_one hβ _).2 hy, rfl⟩

theorem smul_mem_of_latG {W : HSp D} {β : GL (Fin W.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hβ : IsSDFrame W β Λ 1) {y : Fin W.rank → D.host.E} (hy : y ∈ latG W 1) :
    ((Ideal.absNorm D.host.𝔟 : ℕ) : D.host.E) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hx
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
    rw [smul_smul, mul_comm, ← hc]
    exact Λ.smul_mem c ((GlobalTheory.DatumFourier.mem_latG_one hβ _).1 hv)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Λ.smul_mem c hx

variable (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)

def rho (PP : Pl D.host.E) (a : Fin W.rank) : La →+ kP PP :=
  (resS D.host.F PP).toAddMonoidHom.comp (AddMonoidHom.mk' (fun x => ⟨_, hi x a⟩) fun x y => Subtype.ext (by
    change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
    rw [map_add, rowPairing_add]))

theorem rho_apply (PP : Pl D.host.E) (a : Fin W.rank) (x : La) :
    rho W β e ι hi PP a x = resS D.host.F PP ⟨_, hi x a⟩ := rfl

theorem rho_smul (PP : Pl D.host.E) (a : Fin W.rank) (c c' : 𝓞 D.host.E)
    (h : (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) (x : La) :
    rho W β e ι hi PP a (c • x) = Ideal.Quotient.mk _ c' * rho W β e ι hi PP a x := by
  have : (⟨_, hi (c • x) a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi x a⟩ := by
    refine Subtype.ext ?_
    change rowP W β e (ι (c • x)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι x) a
    rw [map_smul, show c • ι x = (c : D.host.E) • ι x from rfl, rowPairing_smul, h]
  rw [rho_apply, rho_apply, this, map_mul, resS_oToS]

theorem rho_eq {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (PP : Pl D.host.E) (hPP : PP ∈ P) (a : Fin W.rank) (x : La)
    (c : 𝓞 D.host.E) (y : Fin W.rank → D.host.E) (hy : pr W β y a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : ι x = D.sp.cm.sig (c : D.host.E) • y) :
    rho W β e ι hi PP a x = Ideal.Quotient.mk _ c * resS D.host.F PP ⟨_, hy⟩ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  have : (⟨_, hi x a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c * (⟨_, h1⟩ * ⟨_, hy⟩) := by
    refine Subtype.ext ?_
    change rowP W β e (ι x) a = eToEAf D (c : D.host.E) * rowP W β e y a
    rw [h, rowPairing_smul]
    congr 2
    exact star_star _
  rw [rho_apply, this, map_mul, map_mul, resS_oToS, h2 PP hPP, one_mul]

theorem rho_onto {Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hβ : IsSDFrame W β Λ 1) (hι : LatEmb W ι)
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hN : ∀ PP ∈ P, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (t : ∀ PP : Pl D.host.E, Fin W.rank → kP PP) : ∃ x, ∀ PP ∈ P, ∀ a, rho W β e ι hi PP a x = t PP a := by
  obtain ⟨n, s', A, B, hs, hAB, hB, -⟩ := exists_dual W β Λ hβ
  choose z hz using fun k => hι.2.ge (smul_mem_latG hβ (hs k))
  have hu : ∀ PP : Pl D.host.E, ∃ u : kP PP, PP ∈ P →
      u * Ideal.Quotient.mk _ ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = 1 := fun PP => by
    by_cases h : PP ∈ P
    · have := PP.isMaximal
      obtain ⟨u, hu⟩ := Ideal.Quotient.exists_inv (mt Ideal.Quotient.eq_zero_iff_mem.1 (hN PP h))
      exact ⟨u, fun _ => (mul_comm _ _).trans hu⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose u hu using hu
  choose c hc using fun k => crt_places P fun PP => u PP * ∑ a', t PP a' * resS D.host.F PP (A a' k)
  choose c' hc' using fun k => exists_sig (c k)
  refine ⟨∑ k, c' k • z k, fun PP hPP a => ?_⟩
  have h1 : ∀ k, rho W β e ι hi PP a (c' k • z k) = ∑ a', t PP a' * (resS D.host.F PP (A a' k) * resS D.host.F PP (B k a)) := by
    intro k
    rw [rho_smul W β e ι hi PP a (c' k) (c k) (by rw [hc']; exact (star_star _).symm),
      rho_eq W β e ι hi he PP hPP a (z k) ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) (s' k) (pr_int hβ (hs k) a) (by
        rw [hz]
        congr 1
        exact ((congrArg _ (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _)).trans (map_natCast _ _)).symm),
      hc k PP hPP, show (⟨_, pr_int hβ (hs k) a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = B k a from
        Subtype.ext (hB k a).symm, mul_mul_mul_comm, hu PP hPP, one_mul, Finset.sum_mul]
    simp only [mul_assoc]
  rw [map_sum]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← RingHom.map_mul, ← map_sum, ← Matrix.mul_apply, hAB, Matrix.one_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg hb, map_zero, mul_zero]) (by simp), if_pos rfl, map_one, mul_one]

theorem rho_ker {Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hβ : IsSDFrame W β Λ 1) (hι : LatEmb W ι)
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (τ : 𝓞 D.host.E →+* 𝓞 D.host.E) (hτ : ∀ c, (τ c : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : ∀ PP ∈ P, ∀ a, rho W β e ι hi PP a x = 0) :
    x ∈ ((∏ PP ∈ P, PP.asIdeal).map τ) • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨n, s', A, B, hs, -, -, hy⟩ := exists_dual W β Λ hβ
  choose z hz using fun k => hι.2.ge (smul_mem_latG hβ (hs k))
  have hcop : ∀ c : 𝓞 D.host.E, (∀ PP ∈ P, c ∈ PP.asIdeal) → c ∈ ∏ PP ∈ P, PP.asIdeal := fun c hc => by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime fun x _ y _ h => HeightOneSpectrum.isCoprime_of_ne _ _ h]
    simpa only [Submodule.mem_iInf] using hc
  set N : ℕ := Ideal.absNorm D.host.ccK
  set m : ℕ := Ideal.absNorm D.host.𝔟
  have hm : ((m : ℕ) : D.host.E) • ι x ∈ Λ := smul_mem_of_latG hβ (hι.2.le (LinearMap.mem_range_self ι x))
  have hcast : ∀ j : ℕ, ((j : 𝓞 D.host.E) : D.host.E) = j := fun j => map_natCast (algebraMap (𝓞 D.host.E) D.host.E) j
  obtain ⟨c, hc1, hc2⟩ := hy _ hm
  have hc : ∀ k, c k ∈ ∏ PP ∈ P, PP.asIdeal := fun k => hcop _ fun PP hPP => by
    have h1 : oToS D.host.F D.host.E (c k) = ∑ a, ⟨_, pr_int hβ hm a⟩ * A a k := by
      refine Subtype.ext ?_
      rw [AddSubmonoidClass.coe_finsetSum]
      exact hc2 k
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← resS_oToS (F := D.host.F), h1, map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h2 := rho_eq W β e ι hi he PP hPP a ((m : 𝓞 D.host.E) • x) 1 _ (pr_int hβ hm a) (by
      rw [map_smul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, map_one, one_smul, ← hcast]; rfl)
    rw [rho_smul W β e ι hi PP a m m (by rw [hcast, map_natCast]), hx PP hPP, mul_zero, map_one, one_mul] at h2
    rw [map_mul, ← h2, zero_mul]
  have h3 : ((N * m : ℕ) : 𝓞 D.host.E) • x = ∑ k, τ (c k) • z k := by
    refine hι.1 ?_
    rw [map_smul, map_sum]
    change (((N * m : ℕ) : 𝓞 D.host.E) : D.host.E) • ι x = _
    rw [hcast, Nat.cast_mul, mul_smul, hc1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hz, smul_comm, ← hτ]
    rfl
  have hu : ∀ PP : Pl D.host.E, ∃ u : kP PP, PP ∈ P →
      Ideal.Quotient.mk _ ((N * m : ℕ) : 𝓞 D.host.E) * u = 1 := fun PP => by
    by_cases h : PP ∈ P
    · have := PP.isMaximal
      have h4 : ((N * m : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h5 => by
        rw [Nat.cast_mul] at h5
        rcases PP.isPrime.mem_or_mem h5 with h5 | h5
        · exact hP PP h (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h5)
        · obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
          exact hP PP h ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h5)).mul_right _))
      obtain ⟨u, hu⟩ := Ideal.Quotient.exists_inv (mt Ideal.Quotient.eq_zero_iff_mem.1 h4)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose u hu using hu
  obtain ⟨v, hv⟩ := crt_places P u
  have h6 : 1 - ((N * m : ℕ) : 𝓞 D.host.E) * v ∈ ∏ PP ∈ P, PP.asIdeal := hcop _ fun PP hPP => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hv PP hPP, hu PP hPP, sub_self]
  have h7 : x = τ (1 - ((N * m : ℕ) : 𝓞 D.host.E) * v) • x + τ v • ((N * m : ℕ) : 𝓞 D.host.E) • x := by
    rw [smul_smul, ← add_smul, map_sub, map_one, map_mul, map_natCast, mul_comm, sub_add_cancel, one_smul]
  rw [h7, h3]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ h6) trivial) (Submodule.smul_mem _ _
    (sum_mem fun k _ => Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hc k)) trivial))

theorem isIntM_frame (i : Fin D.R.m) {β : GL (Fin (Vc D i).rank) (EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} (hV : VStd D i) (hβ : IsSDFrame (Vc D i) β Λ 1) :
    IsIntM β.val := by
  intro j a
  have hmem : (Pi.single j 1 : Fin (Vc D i).rank → D.host.E) ∈ Λ := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ, ← GlobalTheory.SplitReps.hLat_one, hV.2]
    intro k _
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  convert pr_int hβ hmem a using 1
  rw [pr, hV.1, Finset.sum_eq_single j, Finset.sum_eq_single j]
  · simp
  · intro l _ hl; simp [hl]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero, map_zero, zero_mul]
    intro l _
    by_cases hl : l = j
    · subst hl; rw [Matrix.one_apply_ne hk.symm, mul_zero]
    · simp [hl]
  · simp

end Pairing

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem exists_point_phiIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (I : Ideal (𝓞 D.host.E)), LatEmb (Wc D i) ι → HalfIs R A.μ0 l.Mb I → ∃ x1 : Fin (Vc D i).rank → LevQc Dw l, Submodule.span (𝓞 D.host.E) (Set.range x1) = ⊤ ∧ PhiIs R i c.F.val.toRingHom A.μ0 ι (Mfr l • ⊤) (indPhi c x1) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw l c ι I hι hh
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP =>
    (hR.lev.Q_ram A.μ0 PP).2 (Or.inl hP) (by rw [hR.lev.xi_base]; exact fun _ _ => rfl)
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i A.μ0
  have he' : IsIdemSum e R.Pg := by rwa [hQ, Finset.union_empty] at he
  have hP := fun PP (h : PP ∈ R.Pg) => hh.2.2 PP (Or.inl h)
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hR.lev.βV i)
  have hβ' := isIntM_frame i hV (hR.lev.βV i)
  have hi : ∀ x a, LevelDatum.rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    LevelDatum.rowP_int _ _ _ (hR.lev.βW i) e _ he' hP _ (hι.2.le (LinearMap.mem_range_self ι x)) a
  have hτ : ∀ c, ((H.bar c : 𝓞 D.host.E) : D.host.E) = D.sp.cm.sig (c : D.host.E) := fun c => H.bar_eq c
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := (rank_Wc i).le.trans (r_le_V i)
  obtain ⟨x1, h1, h2⟩ := exists_point R.Pg (fun PP => Formalism.L2.DIV.kP PP)
    (fun PP c => Ideal.Quotient.mk PP.asIdeal (H.bar c))
    (fun t => by
      obtain ⟨c, hc⟩ := crt_places R.Pg t
      exact ⟨H.bar.symm c, fun PP h => by rw [RingEquiv.apply_symm_apply]; exact hc PP h⟩)
    (rho (Wc D i) (R.βW i) e ι hi) (fun PP a c x => rho_smul _ _ _ _ hi PP a c _ (hτ c) x) (Mfr l • ⊤)
    (fun x => ⟨fun hx PP hPP a => LevelDatum.residue_rowPairing_eq_zero _ _ e ι a (fun x => hi x a) (Mfr l) PP (fun c hc => by
        obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hc
        rw [hh.1] at hb
        refine ⟨b, Ideal.prod_le_inf.trans (Finset.inf_le hPP) hb, ?_⟩
        change _ = star ((H.bar b : 𝓞 D.host.E) : D.host.E)
        rw [H.bar_eq]
        exact (star_star _).symm) x hx,
      fun hx => by
        rw [Mfr, hh.1]
        exact rho_ker _ _ _ _ hi (hR.lev.βW i) hι he' hP _ hτ x hx⟩)
    (rho_onto _ _ _ _ hi (hR.lev.βW i) hι he' fun PP h h' =>
      hP PP h (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h'))
    (fun PP => Matrix.of fun a b => Formalism.L2.DIV.resS D.host.F PP ⟨_, hβ' a b⟩)
    (fun PP => Matrix.of fun a b => Formalism.L2.DIV.resS D.host.F PP ⟨_, hβ a b⟩)
    (fun PP => by
      ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, ← RingHom.map_mul, ← map_sum]
      have : (∑ j, ⟨_, hβ a j⟩ * ⟨_, hβ' j b⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = if a = b then 1 else 0 := by
        refine Subtype.ext ?_
        rw [AddSubmonoidClass.coe_finsetSum]
        refine (congrFun (congrFun (R.βV i).inv_mul a) b).trans ?_
        rw [Matrix.one_apply]
        split_ifs <;> rfl
      rw [this, Matrix.one_apply]
      split_ifs
      exacts [map_one _, map_zero _]) hrn
  refine ⟨x1, h1, e, he, fun x => ?_⟩
  obtain ⟨h3, h4⟩ := LevelDatum.redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a
  refine ⟨h3, ?_⟩
  have h5 : ((fun b => Submodule.Quotient.mk (x b)) = x1) ↔ ∀ PP ∈ R.Pg,
      LowZero (Wc D i).rank (redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) ∧
      topL (Wc D i).rank (redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) = 1 :=
    (h2 x).trans (forall₂_congr fun PP _ => by
      rw [low_top_iff hrn]
      exact Eq.congr_left (Matrix.ext fun b a => (h4 PP b a).symm))
  rw [hQ, omegaQ, dif_pos (by simp), Finset.attach_empty, Finset.prod_empty, mul_one, omegaK, indPhi]
  by_cases h6 : (fun b => Submodule.Quotient.mk (x b)) = x1
  · rw [if_pos h6, if_pos (h5.1 h6), map_one]
  · rw [if_neg h6, if_neg (mt h5.2 h6), map_zero]

end GlobalTheory.BasePoint

end
