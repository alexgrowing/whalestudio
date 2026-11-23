import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.PushLoc
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.TraceHeckeCongruenceVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Topology

private theorem UpperTheory.Kd.K4.mlT_cpt {l : ℕ} [Fact l.Prime] (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  haveI : ContinuousSMul ℤ_[l] (PadicAlgCl l) := by
    refine ⟨?_⟩
    have : (fun q : ℤ_[l] × PadicAlgCl l => q.1 • q.2) = fun q => (q.1 : ℚ_[l]) • q.2 := by
      funext q; rfl
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  exact Submodule.isCompact_of_fg hfg

private theorem UpperTheory.Kd.K4.mlT_le {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨M, hM⟩ := (UpperTheory.Kd.K4.mlT_cpt c).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
  have := hM _ (c.O.pow_mem ha n)
  rw [norm_pow] at this
  linarith

private theorem UpperTheory.Kd.K4.mlT_lt (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem UpperTheory.Kd.K4.mlT_topSum (hA : SApi) (hI : SInvApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n M : ℕ) {ι : Type} (S : Finset ι)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (h : ∀ i ∈ S, TopCoc X l N w n M (z i)) :
    TopCoc X l N w n M (fun σ => ∑ i ∈ S, z i σ) := by
  classical
  have hsum := (hA Ω ε X l n).2.2.2.1
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact (hI Ω ε X l N w n).2.2.2.2.1 ι S _ fun i hi => (h i hi).inv σ hσ
  · have e : (∑ i ∈ S, z i σ) + X.galB l σ (∑ i ∈ S, z i τ) = ∑ i ∈ S, (z i σ + X.galB l σ (z i τ)) := by
      rw [map_sum, Finset.sum_add_distrib]
    rw [e]
    exact hsum ι S _ _ fun i hi => (h i hi).coc σ hσ τ hτ
  · choose! T hT using fun i hi => (h i hi).loc
    refine ⟨S.biUnion T, fun σ hσ τ hτ hst => ?_⟩
    exact hsum ι S _ _ fun i hi => hT i hi σ hσ τ hτ fun a ha => hst a (Finset.mem_biUnion.2 ⟨i, hi, ha⟩)

private theorem UpperTheory.Kd.K4.mlT_cohSum (hC : SCohApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N) {A : Type} [CommGroup A]
    (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι) (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l)
    (h : ∀ i ∈ S, CohB X l N w n κ (z i) (z' i)) : CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  classical
  have hc := hC Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using hc.1.refl 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hc.2.2.1 _ _ _ _ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))).1

private theorem UpperTheory.Kd.K4.mlT_shSum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (M : ℕ) {ι : Type} (S : Finset ι) (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) :
    shB X l M (fun σ => ∑ i ∈ S, z i σ) = ∑ i ∈ S, shB X l M (z i) := by
  funext s y
  simp [shB, Finset.sum_apply, map_sum]

private theorem UpperTheory.Kd.K4.mlT_pushSum {Γ : Type} [Group Γ] {B A M ι : Type} [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (π : B → A) (S : Finset ι) (f : ι → Γ → B → M) :
    GlobalTheory.KA.push π (∑ i ∈ S, f i) = ∑ i ∈ S, GlobalTheory.KA.push π (f i) := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.sum_apply]
  exact Finset.sum_comm

private theorem UpperTheory.Kd.K4.mlT_lsq (l p : ℕ) (hp : p.Prime) (h : Nat.Coprime p l) (k : ℕ) :
    lsqInv l p k = inv1 p l ^ (2 * k) := by
  haveI := Fact.mk hp
  have hu : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have hu2 : IsUnit ((l : ZMod p) ^ (2 * k)) := hu.pow _
  unfold lsqInv inv1
  rw [dif_pos hu2, dif_pos hu, inv_pow]
  congr 1
  ext
  simp

private def UpperTheory.Kd.K4.mlT_pi (l p r : ℕ) [Fact l.Prime] :
    (ZMod p)ˣ × (ZMod (l ^ (r + 1)))ˣ →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  MonoidHom.prodMap (MonoidHom.id _) (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)

private theorem UpperTheory.Kd.K4.mlT_pi_coe (l p r : ℕ) [Fact l.Prime] : (⇑(mlT_pi l p r)) = Prod.map id (redL l r) := rfl

private theorem UpperTheory.Kd.K4.mlT_pi_surj (l p r : ℕ) [Fact l.Prime] : Function.Surjective (mlT_pi l p r) := by
  rw [mlT_pi_coe]
  refine Function.Surjective.prodMap Function.surjective_id ?_
  exact ZMod.unitsMap_surjective (pow_dvd_pow l (Nat.le_succ r))

private def UpperTheory.Kd.K4.mlT_red (l n r N p : ℕ) :
    (ZMod (lvT l n r N p))ˣ →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  MonoidHom.prod (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p)).toMonoidHom)
    (Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
     (ZMod (l ^ r))).toMonoidHom)

attribute [-instance] GlobalTheory.KZ.ClsMod.neZero_pow

theorem UpperTheory.Kd.K4.mlTOf :
    SymEx → SApi → SInvApi → SBStab → SSlD → SCohApi → SCycZ → STopT → KatoTwistedClassNormCompatibleCyclotomic → KatoTwistedClassCompatibleModPowers → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N] (e : ℕ),
      Nat.Coprime l N → l ≠ 2 → 1 ≤ e → ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ → ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
      (pr : X.Fn l → Fin 2 → Qbar l) (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → ∀ (p : ℕ) [NeZero p], p.Prime → Nat.Coprime p (l * N * c * d) →
      ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZTc X l pr W e ψ N p x c d (2 * e + 1) gm cf c₀ Y ∧ (∀ r s s' y, Y r (s * s') y = Y r s y + rhoK W e ψ s *ᵥ Y r s' (y * cycT l r p s)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (Prod.map id (redL l r)) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro hSym hA hI hBS hS hC hZc hT hNr hNn l _ Ω _ _ _ ε X N _ e hlN hl2 he
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨c₁, hc₁⟩ := UpperTheory.Kd.K4.mlB hA hI hBS hS ε X l N (2 * e - 1) hN
  refine ⟨c₁, fun c₀ hc₀ ι gN A W pr x c d gm ψ cf hAd p _ hp hpc => ?_⟩
  obtain ⟨hc1, hd1, hcc, hdc, hadd, hsm, hint, heq, -, -, hg0, -⟩ := hAd
  have hk : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hcy := (hS Ω ε X N hN).2.2.2.2.2.2.2
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hg0 r₀⟩
  have hLaws : ∃ ws, UpperTheory.V.Z.Kato.Sym.Laws X l c d ws :=
    hSym Ω ε X l c d Fact.out hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hL : LiftsWith X l N (2 * e - 1) (cL X l N (2 * e - 1)) :=
    Classical.epsilon_spec (UpperTheory.Kd.K4.liftH ε X l N (2 * e - 1) hl2 hN hlN ⟨e - 1, by omega⟩)
  have hkm : ∀ r (s t : Ω ≃ₐ[ℚ] Ω), kT l r p (s * t) = kT l r p s * kT l r p t := by
    intro r s t
    simp [kT, (hcy p s).2.1 t, mul_comm]
  let κ : ∀ r, (Ω ≃ₐ[ℚ] Ω) →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ := fun r => MonoidHom.mk' (kT l r p) (hkm r)
  have hκ : ∀ r s, κ r s = kT l r p s := fun _ _ => rfl
  let zz : ℕ → ℕ → (Ω ≃ₐ[ℚ] Ω) → X.Fn l := fun n r σ => ∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ
  let tt : ∀ (_ r : ℕ), (ZMod p)ˣ × (ZMod (l ^ r))ˣ := fun n r => (inv1 p l ^ (2 * (r + n)), 1)
  let Z : ∀ (_ r : ℕ), (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → X.Fn l := fun n r s y =>
    GlobalTheory.KA.push (mlT_red l n r N p) (shB X l (lvT l n r N p) (zz n r)) s (y * tt n r)
  have hZeq : ∀ n r, Z n r = ∑ r₀, YT X l n r N p x c d (2 * e - 1) (gm r₀) := by
    intro n r
    funext s y
    have e1 : shB X l (lvT l n r N p) (zz n r) = ∑ r₀, shB X l (lvT l n r N p) (clsT X l n r N p x c d (2 * e - 1) (gm r₀)) :=
      mlT_shSum X l _ _ _
    simp only [Z, e1, mlT_pushSum, Finset.sum_apply, tt]
    refine Finset.sum_congr rfl fun r₀ _ => ?_
    have e2 : y * (inv1 p l ^ (2 * (r + n)), (1 : (ZMod (l ^ r))ˣ)) = (y.1 * inv1 p l ^ (2 * (r + n)), y.2) :=
      Prod.ext rfl (mul_one _)
    rw [e2]
    rfl
  have hπκ : ∀ r s, mlT_pi l p r (κ (r + 1) s) = κ r s := by
    intro r s
    refine Prod.ext rfl ?_
    change redL l r (cycMod (F := ℚ) (Ω := Ω) l (r + 1) s)⁻¹ = (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹
    rw [(hZc Ω l (r + 1) s).1, (hZc Ω l r s).1, ← (hcy (l ^ (r + 1)) s).2.2.2.2 (l ^ r) (pow_dvd_pow l (Nat.le_succ r))]
    exact map_inv _ _
  have hred : ∀ n r s, mlT_red l n r N p (cycM (lvT l n r N p) s)⁻¹ = κ r s := by
    intro n r s
    rw [map_inv, hκ]
    refine Prod.ext ?_ ?_
    · change (Units.map _ (cycM (lvT l n r N p) s))⁻¹ = (cycM p s)⁻¹
      rw [(hcy (lvT l n r N p) s).2.2.2.2 p]
    · change (Units.map _ (cycM (lvT l n r N p) s))⁻¹ = (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹
      rw [(hZc Ω l r s).1]
      exact congrArg (·⁻¹) ((hcy (lvT l n r N p) s).2.2.2.2 (l ^ r)
        ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p))
  have htop : ∀ n r, TopCoc X l N (2 * e - 1) n (lvT l n r N p) (zz n r) := fun n r =>
    mlT_topSum hA hI X l N _ n _ Finset.univ _ fun r₀ _ => hT Ω ε X l N p x c d _ (gm r₀) (hHyp r₀) hp hpc hLaws hL n r
  have hcr : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (GlobalTheory.KA.push (mlT_pi l p r) (Z n (r + 1))) (Z n r) := by
    intro n r
    rw [hZeq, hZeq, mlT_pi_coe, mlT_pushSum]
    exact mlT_cohSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNr Ω ε X l N p x c d _ (gm r₀) (hHyp r₀) hp hpc hLaws hL n r
  have hcn : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (Z (n + 1) r) (Z n r) := by
    intro n r
    rw [hZeq, hZeq]
    exact mlT_cohSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNn Ω ε X l N p x c d _ (gm r₀) (hHyp r₀) hp hpc hLaws hL n r
  obtain ⟨YB, hYB, hcoc, hcont, hcomp, hlast⟩ := hc₁ c₀ hc₀ (fun r => (ZMod p)ˣ × (ZMod (l ^ r))ˣ) (fun r => mlT_pi l p r) κ
    (fun n r => lvT l n r N p) (fun n r => mlT_red l n r N p) tt zz Z (fun r => mlT_pi_surj l p r) hπκ hred (fun _ _ _ _ => rfl)
    htop hcr hcn
  let prA : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  have hprA : ∀ b, prA b = pr b := fun _ => rfl
  have hpush : ∀ {B A' : Type} [Fintype B] [DecidableEq A'] (π : B → A') (f : (Ω ≃ₐ[ℚ] Ω) → B → X.Fn l) s y,
      pr (GlobalTheory.KA.push π f s y) = GlobalTheory.KA.push π (fun s y => pr (f s y)) s y := by
    intro B A' _ _ π f s y
    exact map_sum prA _ _
  have hln : ∀ n d, d ∈ X.B N l (2 * e - 1) → ∀ i, ‖pr ((l : ℤ_[l]) ^ n • d) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n d hd i
    have e1 : algebraMap ℚ_[l] (Qbar l) (((l : ℤ_[l]) ^ n : ℤ_[l]) : ℚ_[l]) = ((l : ℕ) : Qbar l) ^ n := by simp
    rw [hsm, e1, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mlT_le cf (hint d hd i))
  have hfix : ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ),
      (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
    intro M _ s y
    have h1 : cycM M (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((hcy M 1).2.2.2.1).1 (one_mem _)
    have h2 : cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y = 1 := by
      have := (hcy M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹).2.1 (repM M y)
      rwa [inv_mul_cancel, h1, (hcy M s).2.2.1 y, eq_comm] at this
    rw [(hcy M _).2.2.2.1, (hcy M _).2.1, (hcy M _).2.1, (hcy M s).2.2.1]
    calc cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * cycM M s * (y * (cycM M s)⁻¹)
        = (cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y) * (cycM M s * (cycM M s)⁻¹) := by ac_rfl
      _ = 1 := by rw [h2, mul_inv_cancel, one_mul]
  refine ⟨fun r s y => pr (YB r s y), fun r n => ?_, fun r s s' y => ?_, fun r => ?_, fun r y i => ?_,
    fun r s u i => hint _ (hYB r s u) i⟩
  · obtain ⟨bB, hbB, b, hb, h⟩ := hlast r n
    refine ⟨bB, fun σ hσ => ?_, fun y => pr (b y), fun y i => hint _ (hb y) i, fun s y i => ?_⟩
    · change LiftB X l N (2 * e + 1 - 2) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e + 1 - 2) (gm r₀) σ) (bB σ)
      rw [hk]
      exact hbB σ hσ
    · obtain ⟨dd, hdd, hde⟩ := h s y
      have hty : y * tt n r = (y.1 * lsqInv l p (r + n), y.2) := by
        rw [mlT_lsq l p hp (Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hpc) (r + n)]
        exact Prod.ext rfl (mul_one _)
      have hf : (fun s y => pr (shB X l (lvT l n r N p) bB s y)) = fun s y =>
          rhoK W e ψ (repM (lvT l n r N p) y) *ᵥ pr (bB ((repM (lvT l n r N p) y)⁻¹ * s *
            repM (lvT l n r N p) (y * (cycM (lvT l n r N p) s)⁻¹))) := by
        funext s y
        exact heq _ _ (hbB _ (hfix _ s y)).1
      have hsh : pr (GlobalTheory.KA.push (mlT_red l n r N p) (shB X l (lvT l n r N p) bB) s (y * tt n r)) =
          YfBT X l pr W e ψ n r N p bB s (y.1 * lsqInv l p (r + n), y.2) := by
        rw [hpush, hty, hf]
        rfl
      have hdec : YB r s y = GlobalTheory.KA.push (mlT_red l n r N p) (shB X l (lvT l n r N p) bB) s (y * tt n r) +
          (X.galB l s (b (y * κ r s)) - b y) + (l : ℤ_[l]) ^ n • dd := by
        rw [← hde]; abel
      have hprY : pr (YB r s y) = YfBT X l pr W e ψ n r N p bB s (y.1 * lsqInv l p (r + n), y.2) +
          (rhoK W e ψ s *ᵥ pr (b (y * cycT l r p s)) - pr (b y)) + pr ((l : ℤ_[l]) ^ n • dd) := by
        rw [hdec, hadd, hadd, ← hprA (_ - _), map_sub, hprA, hprA, heq _ _ (hb _), hsh]
        rfl
      change ‖pr (YB r s y) i - (YfBT X l pr W e ψ n r N p bB s (y.1 * lsqInv l p (r + n), y.2) +
        (rhoK W e ψ s *ᵥ pr (b (y * cycT l r p s)) - pr (b y))) i‖ ≤ _
      have e3 : ∀ a b : Fin 2 → Qbar l, (a + b) i - a i = b i := fun a b => by simp
      rw [hprY, e3]
      exact hln n dd hdd i
  · change pr (YB r (s * s') y) = pr (YB r s y) + rhoK W e ψ s *ᵥ pr (YB r s' (y * cycT l r p s))
    rw [hcoc, hadd, heq _ _ (hYB _ _ _)]
    rfl
  · funext s y
    change pr (YB r s y) = GlobalTheory.KA.push (Prod.map id (redL l r)) (fun s y => pr (YB (r + 1) s y)) s y
    rw [hcomp r]
    exact hpush _ _ s y
  · rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε' hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (mlT_lt l)
    rw [← norm_pow] at hn
    filter_upwards [hcont r n s y] with t ht
    obtain ⟨dd, hdd, hde⟩ := ht
    rw [dist_eq_norm]
    have e1 : pr (YB r t y) i - pr (YB r s y) i = pr ((l : ℤ_[l]) ^ n • dd) i := by
      rw [← hde, ← hprA (_ - _), map_sub, hprA, hprA]
      rfl
    rw [e1]
    exact lt_of_le_of_lt (hln n dd hdd i) hn
