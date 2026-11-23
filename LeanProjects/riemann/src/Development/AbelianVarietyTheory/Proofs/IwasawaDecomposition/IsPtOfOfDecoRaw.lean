import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Formalism.LocalToGlobal.Columns.RecLevelLoc
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSOfResSEqZero

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TypeLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem gl_ext {x y : GL (Fin n) (AfE F E)} (h : ∀ v, bc (prV (E := E) v) x = bc (prV (E := E) v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (afsplit_inj _ fun v => ?_))
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => g.1 i j) (h v)

variable [StarRing E] {hc : CMData F E} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_of_decoRaw [IsEmpty Q] {x : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n) {p : DecoF E n ST SG Q}
    (hd : decoRaw ST SG x = p.deco.1) : IsPtOf hc x p := by
  have hN : Formalism.UG.CS.globLat x (Formalism.L2.Col.stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨hx, hN ▸ PtExist.carries_globLat x, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => isEmptyElim P⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact PtExist.hasRes_redA _ ((mem_globLat x v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact PtExist.hasRes_redA _ ((mem_globLat x v).1 hv i)

theorem isPtOf_mul_inv [IsEmpty Q] {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (z : J0 hc n ST) :
    IsPtOf hc (g * z.1⁻¹) (((1, redG hc n ST SG z, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  refine isPtOf_of_decoRaw (mul_mem h.uni (inv_mem (congruence_le_adelic_unitary hc n ST z.2))) ?_
  have := decoRaw_rawSm hc ST SG 1 z g
  rw [map_one, OneMemClass.coe_one, map_one, one_mul, (ColAd.near_of_isPtOf h 0).deco] at this
  exact this

omit [NeZero n] in

theorem glg_free {p : DecoF E n ST SG Q} {a b : GLG E n SG} {c d : GLQ E n Q}
    (h : ((1, a, c) : UF E n × GLG E n SG × GLQ E n Q) • p = ((1, b, d) : UF E n × GLG E n SG × GLQ E n Q) • p) : a = b := by
  funext w
  refine Units.ext (Matrix.ext_of_mulVec_single fun j => ?_)
  obtain ⟨x, -, hx⟩ := p.deco.2.be_surj w (Pi.single j 1)
  have := congrArg (fun q : DecoF E n ST SG Q => q.deco.1.be w x) h
  rw [← hx]
  exact this

variable (hc) in

def RdLev {K : Type} [Field K] (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) : Prop :=
  ∀ (z : GL (Fin n) (AfE F E)) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))), z ∈ UAd hc n → (∀ v ∉ bad, bc (prV (E := E) v) z = 1) →
    (z ∈ U ↔ ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) = ∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹

theorem rdLev_of_reads {X : Fields} {hc : CMData X.F X.E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} [IsEmpty Q]
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (emb : X.K →+* ℂ) {bad : Set (HeightOneSpectrum (𝓞 X.F))}
    {U : Subgroup (GL (Fin n) (AfE X.F X.E))} {chi : U →* ℂˣ} {y k : GL (Fin n) (AfE X.F X.E)} {p : DecoF X.E n ST SG Q}
    (hp : IsPtOf hc (y * k) p) (hk : ∀ v ∈ bad, bc (prV (E := X.E) v) k = 1) (hT : ∀ P ∈ ST, underPl X.F P ∉ bad)
    (hlev : ∀ x q, IsPtOf hc (y * x * k) q → (x ∈ U ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ FrmG.incl Λ Θ κ • p = q))
    (hchr : ∀ (x : U) (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → IsPtOf hc (y * x.1 * k) (FrmG.incl Λ Θ κ • p) →
      ((chi x : ℂˣ) : ℂ) = emb ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K)) :
    RdLev hc U chi bad Λ emb := by
  intro z hz hzU h1
  have hJ : z ∈ J0 hc n ST := by
    refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨hzU, hz, fun P hP => ?_⟩
    rw [rll_redAt_congr n (v := underPl X.F P) rfl _ 1 (by rw [h1 _ (hT P hP)]; exact (map_one _).symm), map_one]
    exact one_mem _
  have hzk : z * k = k * z := gl_ext fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v ∈ bad
    · rw [hk v hv, one_mul, mul_one]
    · rw [h1 v hv, one_mul, mul_one]
  have hq := isPtOf_mul_inv hp (⟨z, hJ⟩ : J0 hc n ST)⁻¹
  rw [show y * k * ((⟨z, hJ⟩ : J0 hc n ST)⁻¹).1⁻¹ = y * z * k by
    rw [Subgroup.coe_inv, inv_inv, mul_assoc, ← hzk, mul_assoc], map_inv] at hq
  have hm : (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ↔ redG hc n ST SG ⟨z, hJ⟩ ∈ Λ.grp :=
    ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ w)⟩
  refine ⟨(hlev z _ hq).trans (Iff.trans ⟨?_, fun h => ⟨(1, ⟨_, inv_mem h⟩, 1), map_one _, rfl⟩⟩ hm.symm), fun hU h => ?_⟩
  · rintro ⟨⟨γ, a, c⟩, hγ, e⟩
    obtain rfl : γ = 1 := Subtype.ext ((toGLm X.E n).injective (hγ.trans (map_one _).symm))
    have := glg_free e
    rw [← inv_mem_iff, ← this]
    exact a.2
  · rw [hchr ⟨z, hU⟩ (1, (⟨_, hm.1 h⟩ : Λ.grp)⁻¹, 1) (map_one _) hq]
    show emb ((Λ.chr (⟨_, hm.1 h⟩ : Λ.grp)⁻¹ * Θ.chr 1 : X.Kˣ) : X.K) = _
    rw [map_one, mul_one, map_inv, Units.val_inv_eq_inv_val, map_inv₀, LevFam.chr_apply, Units.coe_prod, map_prod,
      Finset.prod_inv_distrib]
    rfl

omit [StarRing E] [NeZero n] in

theorem int_iff (v : HeightOneSpectrum (𝓞 F)) (d : GL (Fin n) (v.adicCompletionIntegers F)) (x : Fin n → v.adicCompletion F) :
    (∀ b, x b ∈ v.adicCompletionIntegers F) ↔
      ∀ b, (((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) d)⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F := by
  have key : ∀ (d : GL (Fin n) (v.adicCompletionIntegers F)) (x : Fin n → v.adicCompletion F), (∀ b, x b ∈ v.adicCompletionIntegers F) →
      ∀ b, (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) d).1.mulVec x b ∈ v.adicCompletionIntegers F :=
    fun d x hx b => sum_mem fun c _ => mul_mem (d.1 b c).2 (hx c)
  refine ⟨fun h => by rw [← map_inv]; exact key _ _ h, fun h b => ?_⟩
  have := key d _ h b
  rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem fst_std (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hsp : ∀ a, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : Fin n → v.adicCompletion F) :
    (∃ y ∈ Formalism.L2.Herm.locL v (Formalism.L2.Col.stdLat E n), ∀ b, (sp (y b)).1 = x b) ↔ ∀ b, x b ∈ v.adicCompletionIntegers F := by
  have h := split_integral_local F E v sp hsp
  rw [rll_locL_std]
  constructor
  · rintro ⟨y, hy, e⟩ b
    obtain ⟨s, hs⟩ := hy b (Set.mem_univ b)
    rw [← e, ← hs]
    exact ((h _).1 s.2).1
  · intro hx
    refine ⟨fun b => sp.symm (x b, 0), fun b _ => ⟨⟨_, (h (sp.symm (x b, 0))).2 ?_⟩, rfl⟩, fun b => by simp⟩
    rw [sp.apply_symm_apply]
    exact ⟨hx b, zero_mem _⟩

theorem redM_mat {σ : E →ₐ[F] E} {gp : Fin 2 → ℕ} (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (h : (gp j : 𝓞 F) ∈ v.asIdeal) {w : HeightOneSpectrum (𝓞 E)} (ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)
    (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (hρ : ∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = G.phi j v h (prV (E := E) v s.1))
    (he : ∀ s, IsLocalRing.residue _ (ρ s) = e (resS F w s)) (d : GL (Fin n) (v.adicCompletionIntegers F))
    (z : St (1 : GL (Fin n) (AfE F E))) :
    redM F v (G.mat j v h (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) d) (bc (prV (E := E) v) z.1)) =
      ((bc (IsLocalRing.residue _) d)⁻¹ * bc e.toRingHom (redAt 1 w z) * bc (IsLocalRing.residue _) d : GL (Fin n) (kv F v)).1 := by
  obtain ⟨y, hy, hr⟩ := St_one_int z.2
  have e1 : bc (G.phi j v h) (bc (prV (E := E) v) z.1) =
      bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (bc ρ y) := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show G.phi j v h (prV (E := E) v (z.1.1 a b)) = ((ρ (y.1 a b) : v.adicCompletionIntegers F) : v.adicCompletion F)
    rw [hρ, hy]
  have e2 : bc e.toRingHom (redAt 1 w z) = bc (IsLocalRing.residue _) (bc ρ y) := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show e ((redAt 1 w ⟨z.1, z.2⟩).1 a b) = IsLocalRing.residue _ (ρ (y.1 a b))
    rw [hr, he]
  rw [GLoc.mat, e1, e2, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  exact Formalism.L2.G.redM_bc v _

variable (hc) in

theorem exists_trunc (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : ∀ v ∈ s, x v ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (h2 : ∀ v ∈ s, x v ∈ stabGL (Formalism.L2.Herm.locL v (Formalism.L2.Col.stdLat E n))) :
    ∃ z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n ∧ (∀ v ∈ s, bc (prV (E := E) v) z = x v) ∧
      ∀ v ∉ s, bc (prV (E := E) v) z = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, one_mem _, by simp, fun v _ => map_one _⟩
  | insert a s ha ih =>
    obtain ⟨z, z1, z2, z3, z4⟩ := ih (fun v hv => h1 v (Finset.mem_insert_of_mem hv)) fun v hv => h2 v (Finset.mem_insert_of_mem hv)
    refine ⟨rll_put n a (x a) * z, mul_mem (rll_put_mem_St n a (h2 a (by simp))) z1,
      mul_mem (rll_put_mem_UAd hc n a (h1 a (by simp))) z2, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [rll_put_self, z4 _ ha, mul_one]
      · rw [rll_put_ne n a v (fun e => ha (e ▸ hv)), z3 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, rll_put_ne n a v hv.1, z4 v hv.2, one_mul]

structure Cmp {σ : E →ₐ[F] E} {gp : Fin 2 → ℕ} (G : GLoc F E σ gp) (SG : Finset (HeightOneSpectrum (𝓞 E))) where

  W : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → SG
  ov : ∀ j v h, underPl F (W j v h).1 = v
  uniq : ∀ j v h (w : SG), underPl F w.1 = v → w = W j v h
  all : ∀ w : SG, ∃ j, (gp j : 𝓞 F) ∈ (underPl F w.1).asIdeal
  one : ∀ j j' (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → (gp j' : 𝓞 F) ∈ v.asIdeal → j = j'

  ρ : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal →
    (Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)

  e : ∀ j v h, (𝓞 E ⧸ (W j v h).1.asIdeal) ≃+* kv F v
  ρ_eq : ∀ j v h s, ((ρ j v h s : v.adicCompletionIntegers F) : v.adicCompletion F) = G.phi j v h (prV (E := E) v s.1)
  e_eq : ∀ j v h s, IsLocalRing.residue _ (ρ j v h s) = e j v h (resS F (W j v h).1 s)

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem nonempty_cmp {R : Ranks} (H : Formalism.BasicNotions.Host R) (hc : CMData H.F H.E) {SG : Finset (HeightOneSpectrum (𝓞 H.E))}
    (hl : LevOk H SG ∅) (G : GLoc H.F H.E hc.sig H.g) (hne : H.g 0 ≠ H.g 1)
    (h1 : ∀ w ∈ SG, ∃ j, (H.g j : 𝓞 H.E) ∈ w.asIdeal)
    (h2 : ∀ j (w : HeightOneSpectrum (𝓞 H.E)), cO H.E (G.piG j) ∈ w.asIdeal → w ∈ SG) : Nonempty (Cmp G SG) := by
  classical
  have hu : ∀ w w' : SG, underPl H.F w.1 = underPl H.F w'.1 → w = w' := fun w w' e => by
    rcases (under_eq_iff H w'.1 w.1).1 e with h | h
    · exact Subtype.ext h
    · exact absurd (by simpa only [Finset.union_empty, ← h] using w.2) (hl.split w'.1 (by simpa only [Finset.union_empty] using w'.2))
  have hW : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 H.F)), (H.g j : 𝓞 H.F) ∈ v.asIdeal → ∃ w : SG, underPl H.F w.1 = v := by
    intro j v h
    have := v.isMaximal
    obtain ⟨P, hP, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 H.E) v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 H.F) (𝓞 H.E))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
    let w : HeightOneSpectrum (𝓞 H.E) := ⟨P, hP.isPrime, fun h0 => v.ne_bot (by
      rw [← e, h0]; exact Ideal.comap_bot_of_injective (algebraMap (𝓞 H.F) (𝓞 H.E)) (FaithfulSMul.algebraMap_injective _ _))⟩
    have e' : underPl H.F w = v := HeightOneSpectrum.ext e
    have hg : (H.g j : 𝓞 H.E) ∈ w.asIdeal := by
      rw [← e, Ideal.mem_comap, map_natCast] at h
      exact h
    rcases hl.cover j w hg with h' | h'
    · exact ⟨⟨w, h'⟩, e'⟩
    · exact ⟨⟨_, h'⟩, ((under_eq_iff H w _).2 (Or.inr rfl)).trans e'⟩
  choose W hW using hW
  have hr := fun j v h => GlobalTheory.SplitResidue.exists_residue_equiv H.F H.E v (W j v h).1 (G.phi j v h) (cO H.E (G.piG j))
    (fun a => congrArg Prod.fst (G.sp_alg j v h a)) (G.sp_pi j v h)
    fun P hP hp => congrArg Subtype.val (hu ⟨P, h2 j P hp⟩ (W j v h) (hP.trans (hW j v h).symm))
  choose ρ e hρ he using hr
  refine ⟨⟨W, hW, fun j v h w hw => hu _ _ (hw.trans (hW j v h).symm), fun w => ?_, fun j j' v a b => ?_, ρ, e, hρ, he⟩⟩
  · obtain ⟨j, hj⟩ := h1 w.1 w.2
    exact ⟨j, Ideal.mem_comap.2 (by rwa [map_natCast])⟩
  · by_contra hjj
    have hne' : H.g j ≠ H.g j' := by
      fin_cases j <;> fin_cases j'
      exacts [absurd rfl hjj, hne, hne.symm, absurd rfl hjj]
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (H.g_prime j) (H.g_prime j')).2 hne')).map
      (Int.castRingHom (𝓞 H.F))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa using a)) (Ideal.mul_mem_left _ _ (by simpa using b))

omit [StarRing E] [NeZero n] in

theorem Cmp.prod_eq {σ : E →ₐ[F] E} {gp : Fin 2 → ℕ} {G : GLoc F E σ gp} (C : Cmp G SG) (f : SG → ℂ) :
    ∏ w, f w = ∏ j : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal), f (C.W j v h) := by
  classical
  choose jj hj using C.all
  rw [← Finset.prod_fiberwise Finset.univ jj f]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Finset.univ.filter fun w => jj w = j).image fun w : SG => underPl F w.1),
    Finset.prod_image]
  · refine Finset.prod_congr rfl fun w hw => ?_
    obtain rfl : jj w = j := (Finset.mem_filter.1 hw).2
    rw [finprod_eq_dif, dif_pos (hj w), ← C.uniq _ _ _ w rfl]
  · intro w _ w' _ e
    exact (C.uniq _ _ (hj w') w e).trans (C.uniq _ _ (hj w') w' rfl).symm
  · intro v hv
    have h : (gp j : 𝓞 F) ∈ v.asIdeal := by
      by_contra h
      apply hv
      show (∏ᶠ (h : (gp j : 𝓞 F) ∈ v.asIdeal), f (C.W j v h)) = 1
      rw [finprod_eq_dif, dif_neg h]
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨C.W j v h, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, C.ov j v h⟩)
    exact C.one _ _ v (by have := hj (C.W j v h); rwa [C.ov] at this) h

theorem exists_gLevH {K : Type} [Field K] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (S : StepLevel F E hc.sig J T f bad) {G : GLoc F E hc.sig gp} (C : Cmp G SG)
    (hbad : ∀ v, v ∈ bad ↔ ∃ j, (gp j : 𝓞 F) ∈ v.asIdeal)
    (hL : ∀ v ∈ bad, Formalism.L2.Herm.locL v S.Lb = Formalism.L2.Herm.locL v (Formalism.L2.Col.stdLat E n))
    {Λ : LevFam E K n SG} {emb : K →+* ℂ} (hR : RdLev hc S.U S.chi bad Λ emb)
    (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
    (lam : ∀ j v h, H j v h →* ℂˣ)
    (d : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletionIntegers F))
    (hH : ∀ j v h M, M ∈ (Λ (C.W j v h)).H ↔ bc (C.e j v h).toRingHom M ∈ H j v h)
    (hlam : ∀ j v h M hM hM', ((lam j v h ⟨bc (C.e j v h).toRingHom M, hM'⟩ : ℂˣ) : ℂ) =
      emb (((Λ (C.W j v h)).lam ⟨M, hM⟩ : Kˣ) : K))
    (hd : ∀ j v h, ∀ M ∈ H j v h, Commute (bc (IsLocalRing.residue _) (d j v h)) M) :
    ∃ V : GLevH S G H lam, ∀ j v h, V.fr j v h = bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (d j v h) := by
  classical
  subst hJ
  have hst : ∀ v ∈ bad, ∀ x ∈ levelVL hc.sig 1 v S.Lb, x ∈ stabGL (Formalism.L2.Herm.locL v (Formalism.L2.Col.stdLat E n)) :=
    fun v hv x hx => hL v hv ▸ hx.2
  have hconj : ∀ j v h, ∀ M ∈ H j v h, (bc (IsLocalRing.residue _) (d j v h))⁻¹ * M * bc (IsLocalRing.residue _) (d j v h) = M :=
    fun j v h M hM => by rw [mul_assoc, ← (hd j v h M hM).eq, inv_mul_cancel_left]

  have htr : ∀ x : S.U, ∃ z : St (1 : GL (Fin n) (AfE F E)), (∀ v ∈ bad, bc (prV (E := E) v) z.1 = bc (prV (E := E) v) x.1) ∧
      ∃ h : ∀ w : SG, redAt 1 w.1 z ∈ (Λ w).H, ((S.chi x : ℂˣ) : ℂ) = ∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹ := by
    intro x
    have hx := ((S.U_eq x.1).1 x.2).2
    have hs : ∀ v, v ∈ (Finset.univ.image fun w : SG => underPl F w.1) ↔ v ∈ bad := fun v => by
      rw [hbad, Finset.mem_image]
      exact ⟨by rintro ⟨w, -, rfl⟩; exact C.all w, fun ⟨j, h⟩ => ⟨_, Finset.mem_univ _, C.ov j v h⟩⟩
    obtain ⟨z, z1, z2, z3, z4⟩ := exists_trunc hc (fun v => bc (prV (E := E) v) x.1) (Finset.univ.image fun w : SG => underPl F w.1)
      (fun v _ => S.Uloc_le v (hx v)) fun v hv => hst v ((hs v).1 hv) _ (S.Uloc_lev v (hx v))
    simp only [hs] at z3 z4
    have hU : z ∈ S.U := (S.U_eq z).2 ⟨z2, fun v => by
      by_cases hv : v ∈ bad
      · rw [z3 v hv]; exact hx v
      · rw [z4 v hv]; exact one_mem _⟩
    obtain ⟨r1, r2⟩ := hR z z1 z2 z4
    refine ⟨⟨z, z1⟩, z3, r1.1 hU, ?_⟩
    rw [← r2 hU]
    have := S.chi_triv ((⟨z, hU⟩ : S.U)⁻¹ * x) fun v hv => by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, z3 v hv, inv_mul_cancel]
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    rw [this]
  choose z hz hm hchi using htr
  refine ⟨⟨fun j v h => bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (d j v h), fun j v h x => ?_,
    fun j v h x hx => ?_, fun j v h x => ⟨_, (hH j v h _).1 (hm x (C.W j v h))⟩, fun j v h x => ?_, fun x => ?_, fun x => ?_⟩,
    fun _ _ _ => rfl⟩
  · rw [← int_iff, ← fst_std v (G.sp j v h) (G.sp_alg j v h), ← hL v ((hbad v).2 ⟨j, h⟩)]
    rfl
  · have hv := (hbad v).2 ⟨j, h⟩
    have hS := rll_put_mem_St n v (hst v hv x hx)
    have hA := rll_put_mem_UAd hc n v hx.1
    have h1 : x ∈ S.Uloc v ↔ rll_put n v x ∈ S.U := by
      rw [S.U_eq]
      refine ⟨fun h' => ⟨hA, fun v' => ?_⟩, fun h' => rll_put_self n v x ▸ h'.2 v⟩
      by_cases e : v' = v
      · subst e; rwa [rll_put_self]
      · rw [rll_put_ne n v v' e]; exact one_mem _
    have h2 := redM_mat G j v h _ _ (C.ρ_eq j v h) (C.e_eq j v h) (d j v h) ⟨_, hS⟩
    rw [rll_put_self] at h2
    rw [h1, (hR _ hS hA fun v' hv' => rll_put_ne n v v' (fun e => hv' (e ▸ hv)) x).1, h2]
    constructor
    · intro h'
      have h3 := (hH j v h _).1 (h' (C.W j v h))
      exact ⟨_, h3, by rw [hconj j v h _ h3]⟩
    · rintro ⟨M, hM, e⟩ w
      by_cases hw : w = C.W j v h
      · subst hw
        have e' := Units.ext e
        rw [← hconj j v h M hM, mul_left_inj, mul_right_inj] at e'
        rw [hH, ← e']
        exact hM
      · rw [rll_put_red n v x hS w.1 fun ho => hw (C.uniq j v h w (HeightOneSpectrum.ext ho.symm))]
        exact one_mem _
  · rw [← hz x v ((hbad v).2 ⟨j, h⟩), redM_mat G j v h _ _ (C.ρ_eq j v h) (C.e_eq j v h),
      hconj j v h _ ((hH j v h _).1 (hm x _))]
  · rw [hchi, C.prod_eq]
    simp only [hlam _ _ _ _ (hm x _)]
  · rw [hchi, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    have h1 := (emb.toMonoidHom.comp ((Units.coeHom K).comp (Λ w).lam)).isOfFinOrder (isOfFinOrder_of_finite ⟨_, hm x w⟩)
    rw [norm_inv, inv_eq_one]
    exact h1.norm_eq_one

theorem locL_eq (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 E) (Fin n → E)} {t : 𝓞 E}
    (hL : ∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) {d : 𝓞 F} (hd : d ∉ v.asIdeal)
    (ht : t ∣ algebraMap (𝓞 F) (𝓞 E) d) : Formalism.L2.Herm.locL v L = Formalism.L2.Herm.locL v (Formalism.L2.Col.stdLat E n) := by
  refine le_antisymm (rll_latS_mono n v fun x hx => (mem_stdLat x).2 fun i => ?_) (rll_locL_le_of_smul n v hd fun l hl => ?_)
  · obtain ⟨r, hr, -⟩ := (hL x).1 hx i
    exact ⟨r, hr.symm⟩
  · choose r hr using (mem_stdLat l).1 hl
    refine (hL _).2 fun j => ⟨algebraMap (𝓞 F) (𝓞 E) d * r j, ?_, fun _ => ht.mul_right _⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← hr, ← map_mul]

section Mat

variable {κ κ' K : Type} [Field κ] [Field κ'] [Field K] {n k rS t : ℕ} {zl : Bool}

theorem inJSym_map (e : κ →+* κ') (M : Matrix (Fin n) (Fin n) κ) : InJSym k rS t zl (M.map e) ↔ InJSym k rS t zl M := by
  have h : ∀ (a : κ) (p : Prop) [Decidable p], (e a = if p then 1 else 0) ↔ a = if p then 1 else 0 := fun a p _ => by
    split_ifs
    · exact map_eq_one_iff e e.injective
    · exact map_eq_zero_iff e e.injective
  simp only [InJSym, Matrix.map_apply, h, map_eq_one_iff e e.injective, map_eq_zero_iff e e.injective]

theorem exists_lam (e : κ ≃+* κ') (emb : K →+* ℂ) (l : Lev κ K n) (g : Matrix (Fin n) (Fin n) κ' → ℂ)
    (hH : ∀ M, M ∈ l.H ↔ M ∈ JSymG κ n k rS t zl) (hl : ∀ M : l.H, emb ((l.lam M : Kˣ) : K) = g (M.1.1.map e)) :
    ∃ lam : JSymG κ' n k rS t zl →* ℂˣ, (∀ M, ((lam M : ℂˣ) : ℂ) = g M.1.1) ∧
      (∀ M, M ∈ l.H ↔ bc e.toRingHom M ∈ JSymG κ' n k rS t zl) ∧
      ∀ M hM hM', ((lam ⟨bc e.toRingHom M, hM'⟩ : ℂˣ) : ℂ) = emb ((l.lam ⟨M, hM⟩ : Kˣ) : K) := by
  have h1 : ∀ M, M ∈ l.H ↔ bc e.toRingHom M ∈ JSymG κ' n k rS t zl := fun M =>
    (hH M).trans (and_congr (inJSym_map e.toRingHom _) (inJSym_map e.toRingHom _)).symm
  have h2 : ∀ M : GL (Fin n) κ', bc e.toRingHom (bc e.symm.toRingHom M) = M := fun M =>
    Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  let lam : JSymG κ' n k rS t zl →* ℂˣ := (Units.map emb.toMonoidHom).comp (l.lam.comp
    (((bc e.symm.toRingHom).comp (Subgroup.subtype _)).codRestrict l.H fun M => (h1 _).2 ((h2 M.1).symm ▸ M.2)))
  have h3 : ∀ M, ((lam M : ℂˣ) : ℂ) = g M.1.1 := fun M => (hl _).trans (congrArg g (congrArg Units.val (h2 M.1)))
  exact ⟨lam, h3, h1, fun M hM hM' => (h3 _).trans (hl ⟨M, hM⟩).symm⟩

def lastDiag {A : Type} [CommRing A] (n : ℕ) (u : Aˣ) : GL (Fin n) A :=
  ⟨diagonal fun i => if i.1 + 1 = n then u.1 else 1, diagonal fun i => if i.1 + 1 = n then u⁻¹.1 else 1,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp⟩

theorem lastDiag_commute {A : Type} [CommRing A] (φ : A →+* κ) (u : Aˣ) {M : GL (Fin n) κ} (hM : M ∈ JSymG κ n k rS t true) :
    Commute (bc φ (lastDiag n u)) M := by
  have h := hM.1.2.2.2 rfl
  have e : (bc φ (lastDiag n u)).1 = diagonal fun i : Fin n => φ (if i.1 + 1 = n then u.1 else 1) :=
    Matrix.diagonal_map (map_zero φ)
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, e, diagonal_mul, mul_diagonal]
  by_cases hij : i = j
  · rw [hij, mul_comm]
  by_cases hi : i.1 + 1 = n
  · rw [(h j i hi).2, if_neg (Ne.symm hij), mul_zero, zero_mul]
  by_cases hj : j.1 + 1 = n
  · rw [(h i j hj).1, if_neg hij, mul_zero, zero_mul]
  · rw [if_neg hi, if_neg hj, mul_comm]

end Mat

end GlobalTheory.Mem.Col2.TypeLev
