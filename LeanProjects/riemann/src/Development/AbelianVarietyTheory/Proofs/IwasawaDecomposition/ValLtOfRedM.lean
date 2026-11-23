import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc

noncomputable section

namespace GlobalTheory.Mem.Col2.ChartLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.UG.P Formalism.L2.Forms Matrix
open scoped TensorProduct

section Red

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem redM_map (X : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) :
    redM F v (X.map (v.adicCompletionIntegers F).subtype) = X.map (IsLocalRing.residue _) := by
  ext a b
  exact dif_pos (X a b).2

theorem exists_map {X : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (h : ∀ a b, X a b ∈ v.adicCompletionIntegers F) :
    ∃ X' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), X'.map (v.adicCompletionIntegers F).subtype = X :=
  ⟨Matrix.of fun a b => ⟨X a b, h a b⟩, rfl⟩

theorem redM_mul {X Y : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hX : ∀ a b, X a b ∈ v.adicCompletionIntegers F)
    (hY : ∀ a b, Y a b ∈ v.adicCompletionIntegers F) : redM F v (X * Y) = redM F v X * redM F v Y := by
  obtain ⟨X', rfl⟩ := exists_map v hX
  obtain ⟨Y', rfl⟩ := exists_map v hY
  rw [← Matrix.map_mul, redM_map, redM_map, redM_map, Matrix.map_mul]

theorem redM_one : redM F v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
  rw [← Matrix.map_one (v.adicCompletionIntegers F).subtype (map_zero _) (map_one _), redM_map,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_lt_of_redM {X : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hX : ∀ a b, X a b ∈ v.adicCompletionIntegers F)
    (h : redM F v X = 1) (a b : Fin n) : Valued.v ((X - 1) a b) < 1 := by
  obtain ⟨X', rfl⟩ := exists_map v hX
  rw [redM_map] at h
  have h1 : (X' - 1).map (IsLocalRing.residue _) = 0 := by
    rw [Matrix.map_sub _ (map_sub _), h, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
  have h2 : IsLocalRing.residue _ ((X' - 1) a b) = 0 := congrFun (congrFun h1 a) b
  rw [IsLocalRing.residue_eq_zero_iff] at h2
  have h3 : X'.map (v.adicCompletionIntegers F).subtype - 1 = (X' - 1).map (v.adicCompletionIntegers F).subtype := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h3]
  exact (Valuation.mem_maximalIdeal_iff _ _).1 h2

end Red

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}

theorem mem_intV_iff (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (x : E ⊗[F] v.adicCompletion F) : x ∈ intV E v ↔
      (G.sp j v h x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp j v h x).2 ∈ v.adicCompletionIntegers F :=
  split_integral_local F E v (G.sp j v h) (G.sp_alg j v h) x

theorem mat_one (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : G.mat j v h 1 x = x.1.map (G.phi j v h) := by
  unfold GLoc.mat
  rw [inv_one, one_mul, mul_one]
  rfl

def emb (v : HeightOneSpectrum (𝓞 F)) : GL (Fin n) (E ⊗[F] v.adicCompletion F) →* GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  toFun x := afsplitU v x 1
  map_one' := Units.ext (afsplitC_one v)
  map_mul' x y := by rw [← afsplitU_mul, one_mul]

theorem emb_self (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) v) (emb v x) = x := afsplit_right1 v x 1

theorem emb_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) w) (emb v x) = 1 := by
  apply Units.ext
  rw [afsplit_coe_bc_prV]
  show (afsplitC v _ _).map _ = _
  rw [afsplitC_prV_ne v w h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def embU (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) : S.Uloc v →* S.U :=
  ((emb v).comp (S.Uloc v).subtype).codRestrict S.U fun x => (S.U_eq _).2
    ⟨afsplitU_mem v σ J _ _ (S.Uloc_le v x.2) (one_mem _), fun w => by
      show bc (prV (E := E) w) (emb v x.1) ∈ _
      by_cases hw : w = v
      · subst hw
        rw [emb_self]
        exact x.2
      · rw [emb_ne hw]
        exact one_mem _⟩

def cmp (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) : S.U →* S.Uloc v :=
  ((bc (prV (E := E) v)).comp S.U.subtype).codRestrict (S.Uloc v) fun x => ((S.U_eq _).1 x.2).2 v

theorem chi_eq_prod (S : StepLevel F E σ J T f bad) (s : Finset (HeightOneSpectrum (𝓞 F))) (x : S.U)
    (hx : ∀ w ∈ bad, w ∉ s → bc (prV (E := E) w) x.1 = 1) : S.chi x = ∏ v ∈ s, S.chi (embU S v (cmp S v x)) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => exact S.chi_triv x fun w hw => hx w hw (Finset.notMem_empty _)
  | insert a s ha ih =>
    have e : ∀ w, w ≠ a → bc (prV (E := E) w) ((embU S a (cmp S a x))⁻¹ * x).1 = bc (prV (E := E) w) x.1 := fun w hw => by
      show bc (prV (E := E) w) ((emb a _)⁻¹ * x.1) = _
      rw [map_mul, map_inv, emb_ne hw, inv_one, one_mul]
    have h1 := ih ((embU S a (cmp S a x))⁻¹ * x) fun w hw hws => by
      by_cases hwa : w = a
      · subst hwa
        show bc (prV (E := E) w) ((emb w _)⁻¹ * x.1) = _
        rw [map_mul, map_inv, emb_self]
        exact inv_mul_cancel _
      · rw [e w hwa]
        exact hx w hw (by simp [hwa, hws])
    rw [Finset.prod_insert ha, map_mul, map_inv, inv_mul_eq_iff_eq_mul] at *
    rw [h1]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    congr 2
    exact Subtype.ext (e w fun h => ha (h ▸ hw))

theorem int_of_mem {v : HeightOneSpectrum (𝓞 F)} {Lb : Submodule (𝓞 E) (Fin n → E)}
    (hL : latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v))
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Lb) (a b : Fin n) : x.1 a b ∈ intV E v := by
  have h2 : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := hx.2
  rw [hL] at h2
  exact ((afsplit_stab_iff _ _).1 h2).1 a b

def redHom (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (J : Matrix (Fin n) (Fin n) E) {Lb : Submodule (𝓞 E) (Fin n → E)}
    (hL : latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v)) :
    levelVL σ J v Lb →* GL (Fin n) (kv F v) :=
  MonoidHom.toHomUnits
    { toFun := fun x => redM F v (G.mat j v h 1 x.1)
      map_one' := by
        rw [mat_one]
        show redM F v ((1 : Matrix (Fin n) (Fin n) _).map _) = 1
        rw [Matrix.map_one _ (map_zero _) (map_one _), redM_one]
      map_mul' := fun x y => by
        simp only [mat_one]
        show redM F v ((x.1.1 * y.1.1).map _) = _
        rw [Matrix.map_mul]
        exact redM_mul v (fun a b => ((mem_intV_iff G j v h _).1 (int_of_mem hL x.2 a b)).1)
          (fun a b => ((mem_intV_iff G j v h _).1 (int_of_mem hL y.2 a b)).1) }

theorem redHom_coe (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (J : Matrix (Fin n) (Fin n) E) {Lb : Submodule (𝓞 E) (Fin n → E)}
    (hL : latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v)) (x : levelVL σ J v Lb) :
    (redHom G j v h J hL x).1 = redM F v (G.mat j v h 1 x.1) := rfl

theorem exists_lift {A B : Type} [Group A] [Group B] (r : A →* B) (c : A →* ℂˣ) (h : ∀ x, r x = 1 → c x = 1) :
    ∃ lam : r.range →* ℂˣ, ∀ x, lam (r.rangeRestrict x) = (c x)⁻¹ := by
  refine ⟨r.rangeRestrict.liftOfRightInverse (Function.surjInv r.rangeRestrict_surjective)
    (Function.rightInverse_surjInv _) ⟨c⁻¹, fun x hx => ?_⟩, fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  rw [MonoidHom.ker_rangeRestrict] at hx
  rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h x hx, inv_one]

theorem exists_gLevH (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) (hg0 : ∀ j, gp j ≠ 0) (hg : Nat.Coprime (gp 0) (gp 1))
    (hbad : ∀ v ∈ bad, (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
    (hL : ∀ j (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal →
      latS (F := F) (v.adicCompletion F) (intV E v) S.Lb = Formalism.UG.stdLat (intV E v))
    (hK : ∀ j v h (x : levelVL σ J v S.Lb), redHom G j v h J (hL j v h) x = 1 →
      ∃ hx : emb v x.1 ∈ S.U, S.chi ⟨_, hx⟩ = 1) :
    ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
      (lam : ∀ j v h, H j v h →* ℂˣ), Nonempty (GLevH S G H lam) := by
  classical
  let r : ∀ j (v : HeightOneSpectrum (𝓞 F)), (gp j : 𝓞 F) ∈ v.asIdeal → (S.Uloc v →* GL (Fin n) (kv F v)) :=
    fun j v h => (redHom G j v h J (hL j v h)).comp (Subgroup.inclusion (S.Uloc_lev v))
  have hlam : ∀ j v h, ∃ lam : (r j v h).range →* ℂˣ, ∀ x, lam ((r j v h).rangeRestrict x) = (S.chi (embU S v x))⁻¹ :=
    fun j v h => exists_lift (r j v h) (S.chi.comp (embU S v)) fun x hx => (hK j v h _ hx).2
  choose lam hlam using hlam
  have hfin : ∀ j, {v : HeightOneSpectrum (𝓞 F) | (gp j : 𝓞 F) ∈ v.asIdeal}.Finite := fun j => by
    have h0 : Ideal.span {(gp j : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hg0 j
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hdis : Disjoint {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal} {v | (gp 1 : 𝓞 F) ∈ v.asIdeal} := by
    rw [Set.disjoint_left]
    intro v h0 h1
    obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hg).map (Int.castRingHom (𝓞 F))
    simp only [eq_intCast, Int.cast_natCast] at e
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  have hchi : ∀ x : S.U, S.chi x = ∏ v ∈ ((hfin 0).union (hfin 1)).toFinset, S.chi (embU S v (cmp S v x)) := fun x =>
    chi_eq_prod S _ x fun w hw hn => absurd (((hfin 0).union (hfin 1)).mem_toFinset.2 (hbad w hw)) hn
  refine ⟨fun j v h => (r j v h).range, lam, ⟨
    { fr := fun _ _ _ => 1
      fr_lat := fun j v h x => ?_
      mem := fun j v h x hx => ?_
      red := fun j v h x => (r j v h).rangeRestrict (cmp S v x)
      red_eq := fun j v h x => rfl
      chi_eq := fun x => ?_
      chi_unit := fun x => ?_ }⟩⟩
  · rw [hL j v h, inv_one, Units.val_one, Matrix.one_mulVec]
    simp only [afsplit_mem_stdLat]
    constructor
    · rintro ⟨y, hy, e⟩ b
      rw [← e b]
      exact ((mem_intV_iff G j v h _).1 (hy b)).1
    · intro hx
      refine ⟨fun b => (G.sp j v h).symm (x b, 0), fun b => (mem_intV_iff G j v h _).2 ?_, fun b => ?_⟩
      · rw [RingEquiv.apply_symm_apply]
        exact ⟨hx b, zero_mem _⟩
      · exact congrArg Prod.fst ((G.sp j v h).apply_symm_apply _)
  · constructor
    · intro hU
      exact ⟨r j v h ⟨x, hU⟩, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, e⟩
      have e1 : redHom G j v h J (hL j v h) ⟨y.1, S.Uloc_lev v y.2⟩ = redHom G j v h J (hL j v h) ⟨x, hx⟩ := Units.ext e
      obtain ⟨h1, -⟩ := hK j v h ((⟨y.1, S.Uloc_lev v y.2⟩ : levelVL σ J v S.Lb)⁻¹ * ⟨x, hx⟩)
        (by rw [map_mul, map_inv, e1, inv_mul_cancel])
      have h2 := ((S.U_eq _).1 h1).2 v
      rw [emb_self] at h2
      have h3 := (S.Uloc v).mul_mem y.2 h2
      rwa [show y.1 * ((⟨y.1, S.Uloc_lev v y.2⟩ : levelVL σ J v S.Lb)⁻¹ * ⟨x, hx⟩).1 = x from mul_inv_cancel_left _ _] at h3
  · simp only [hlam, Units.val_inv_eq_inv_val, inv_inv]
    rw [Fin.prod_univ_two, hchi x, Units.coe_prod]
    have := finprod_mem_union (f := fun v => ((S.chi (embU S v (cmp S v x)) : ℂˣ) : ℂ)) hdis (hfin 0) (hfin 1)
    rw [finprod_mem_eq_finite_toFinset_prod _ ((hfin 0).union (hfin 1))] at this
    exact this
  · rw [hchi x, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    have hj : ∃ j, (gp j : 𝓞 F) ∈ v.asIdeal := by
      rcases ((hfin 0).union (hfin 1)).mem_toFinset.1 hv with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨j, h⟩ := hj
    haveI : Finite (kv F v) := glint_finite_residueField v
    have h1 : IsOfFinOrder (lam j v h ((r j v h).rangeRestrict (cmp S v x))) := (lam j v h).isOfFinOrder (isOfFinOrder_of_finite _)
    rw [hlam, isOfFinOrder_inv_iff] at h1
    exact ((Units.coeHom ℂ).isOfFinOrder h1).norm_eq_one

end Gen

section Small

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Chr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {gp : Fin 2 → ℕ}

theorem latS_eq_std {Lb : Submodule (𝓞 E) (Fin n → E)} {T : ℕ} {v : HeightOneSpectrum (𝓞 F)} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Lb) :
    latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, afsplit_mem_stdLat]
    intro i
    obtain ⟨r, hr⟩ := h1 x hx i
    exact easyc_inclE_mem _ _ (x i) ⟨r, hr.symm⟩
  · intro x hx
    rw [afsplit_mem_stdLat] at hx
    have hv : Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
      have e : ((T : ℕ) : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (T : 𝓞 F)) := by simp
      rw [e, valued_algebraMap, HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact hT
    have h0 : ((T : ℕ) : v.adicCompletion F) ≠ 0 := fun h => by simp [h] at hv
    have hi : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
      Subring.subset_closure (Or.inr ⟨⟨_, by
        show _ ∈ v.adicCompletionIntegers F
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]⟩, rfl⟩)
    have hone : ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) * ((T : ℕ) : E ⊗[F] v.adicCompletion F) = 1 := by
      rw [← map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F),
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ h0, one_mul]
      rfl
    have hx' : x = ∑ i, (⟨x i * _, mul_mem (hx i) hi⟩ : intV E v) •
        (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i (T : E) : Fin n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, map_natCast]
        show _ = x j * _ * _
        rw [mul_assoc, hone, mul_one]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 i, rfl⟩)

theorem val_adAt_lt (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {z : E ⊗[F] v.adicCompletion F} (h1 : Valued.v (G.sp j v h z).1 < 1) (h2 : Valued.v (G.sp j v h z).2 < 1)
    (P : HeightOneSpectrum (𝓞 E)) : Valued.v (adAt F P (afsplitIE v z)) < 1 := by
  have ha : ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal ∧ a ≠ 0 ∧
      ∀ t : v.adicCompletion F, Valued.v t < 1 → Valued.v t ≤ v.intValuation a := by
    by_cases hP : P.under (𝓞 F) = v
    · obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
      refine ⟨a, ?_, ?_, fun t ht => ?_⟩
      · have : a ∈ (P.under (𝓞 F)).asIdeal := by
          rw [hP, ← HeightOneSpectrum.intValuation_lt_one_iff_mem, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num
        exact this
      · rintro rfl
        simp at ha
        exact WithZero.exp_ne_zero ha.symm
      · rw [ha]
        by_cases h0 : Valued.v t = 0
        · simp [h0]
        · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
          rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
          omega
    · have hn : ¬ (P.under (𝓞 F)).asIdeal ≤ v.asIdeal := fun hle =>
        hP (HeightOneSpectrum.ext ((P.under (𝓞 F)).isMaximal.eq_of_le v.isPrime.ne_top hle))
      obtain ⟨a, haP, hav⟩ := SetLike.not_le_iff_exists.1 hn
      refine ⟨a, haP, fun e => hav (e ▸ zero_mem _), fun t ht => ?_⟩
      rw [(HeightOneSpectrum.intValuation_eq_one_iff).2 hav]
      exact ht.le
  obtain ⟨a, haP, ha0, ha⟩ := ha
  set α : v.adicCompletion F := algebraMap F _ (algebraMap (𝓞 F) F a) with hα
  have hvα : Valued.v α = v.intValuation a := by rw [hα, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have hv0 : Valued.v α ≠ 0 := by rw [hvα]; exact v.intValuation_ne_zero a ha0
  have hα0 : α ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have key : ∀ t : v.adicCompletion F, Valued.v t < 1 → α⁻¹ * t ∈ v.adicCompletionIntegers F := fun t ht => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hv0), mul_one, hvα]
    exact ha t ht
  have hy : ((1 : E) ⊗ₜ[F] α⁻¹) * z ∈ intV E v := by
    rw [mem_intV_iff G j v h, map_mul, G.sp_alg]
    exact ⟨key _ h1, key _ h2⟩
  set e : E := algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) with he
  have hz : z = prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) * (((1 : E) ⊗ₜ[F] α⁻¹) * z) := by
    have : prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = (1 : E) ⊗ₜ[F] α := by
      rw [afsplit_prV_inclE]
      have e1 : e = algebraMap F E (algebraMap (𝓞 F) F a) := rfl
      show e ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [e1, hα, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := v.adicCompletion F), TensorProduct.smul_tmul]
    rw [this, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hα0, one_mul]
    exact (one_mul z).symm
  rw [hz, map_mul, afsplit_decomp, mul_comm (afsplitEps E v), mul_assoc, afsplit_eps_mul_IE, map_mul, map_mul, adAt_inclE,
    valued_algebraMap]
  refine mul_lt_one_of_lt_of_le ?_ ((mem_rInt_iff F E _).1 (afsplit_IE_int v _ hy) P)
  rw [he, HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact haP

theorem val_emb_lt (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {Lb : Submodule (𝓞 E) (Fin n → E)}
    (hL : latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v))
    (x : levelVL σ J v Lb) (hx : redHom G j v h J hL x = 1) (P : HeightOneSpectrum (𝓞 E)) (a b : Fin n) :
    Valued.v (adAt F P ((((emb v x.1)⁻¹).1 - 1) a b)) < 1 := by
  subst hJ
  have hs : ∀ y : levelVL σ 1 v Lb, redHom G j v h 1 hL y = 1 → ∀ a b, Valued.v ((y.1.1.map (G.phi j v h) - 1) a b) < 1 :=
    fun y hy => val_lt_of_redM v (fun a b => ((mem_intV_iff G j v h _).1 (int_of_mem hL y.2 a b)).1)
      (by rw [← mat_one, ← redHom_coe G j v h 1 hL, hy, Units.val_one])
  have e : (((emb v x.1)⁻¹).1 - 1) a b = afsplitIE v (((x.1⁻¹).1 - 1) a b) := by
    rw [← map_inv, ← afsplitC_one v]
    show afsplitC v _ _ a b - afsplitC v _ _ a b = _
    rw [afsplitC_apply, afsplitC_apply, Matrix.sub_apply, map_sub, Units.val_one]
    ring
  rw [e]
  have hone : ∀ (ψ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (M : Matrix (Fin n) (Fin n) _),
      ψ ((M - 1) a b) = (M.map ψ - 1) a b := fun ψ M => by
    rw [← Matrix.map_one ψ (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub _)]
    rfl
  refine val_adAt_lt G j v h ?_ ?_ P
  · have := hs x⁻¹ (by rw [map_inv, hx, inv_one]) a b
    rw [← hone] at this
    exact this
  · have hu := levelvsplit_unitary _ (G.sp j v h) (G.sp_sig j v h) _ x.1⁻¹ (x⁻¹).2.1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)] at hu
    have h3 := levelvsplit_solve 1 1 _ (x.1.1.map (G.phi j v h)) _ (mul_one _) (by
      show (x.1⁻¹).1.map (G.phi j v h) * _ = _
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]) hu
    have h4 := hone ((RingHom.snd _ _).comp (G.sp j v h).toRingHom) (x.1⁻¹).1
    rw [h3, one_mul, mul_one] at h4
    have h5 := hs x hx b a
    show Valued.v (((RingHom.snd _ _).comp (G.sp j v h).toRingHom) _) < 1
    rw [h4]
    convert h5 using 2
    simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_mul (hQ : Q = ∅) {g k : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p)
    (hu : k ∈ Formalism.L2.Herm.UstdAf hc n) (h1 : ∀ a b, k.1 a b ∈ RInt F E) (h2 : ∀ a b, (k⁻¹).1 a b ∈ RInt F E)
    (h3 : ∀ P a b, Valued.v (adAt F P (((k⁻¹).1 - 1) a b)) < 1) : IsPtOf hc (g * k) p := by
  have hpull : ∀ x, pullV (g * k) x = (k⁻¹).1 *ᵥ pullV g x := fun x => by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
  have hres : ∀ P, ∀ x ∈ p.deco.1.N, ∀ i c, HasRes P (adAt F P (pullV g x i)) c → HasRes P (adAt F P (pullV (g * k) x i)) c := by
    rintro P x hx i c ⟨r, hr, hv⟩
    refine ⟨r, hr, ?_⟩
    have hint : pullV g x ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := (h.lat _).1 (Submodule.subset_span ⟨_, hx, rfl⟩)
    have e : pullV (g * k) x i = pullV g x i + ∑ j, ((k⁻¹).1 - 1) i j * pullV g x j := by
      rw [hpull]
      show _ = _ + (((k⁻¹).1 - 1) *ᵥ pullV g x) i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, add_sub_cancel]
    rw [e, map_add, add_sub_right_comm]
    refine Valuation.map_add_lt _ hv ?_
    rw [map_sum]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul, map_mul]
    exact mul_lt_one_of_lt_of_le (h3 P i j) (DetSpec.val_le_of_mem_hatL P hint j)
  refine ⟨mul_mem h.uni hu, fun x => (h.lat x).trans ?_, fun P x hx i hi => hres _ x hx i _ (h.f P x hx i hi),
    fun w x hx i => hres _ x hx i _ (h.be w x hx i), fun P => absurd P.2 (by simp [hQ])⟩
  have e0 : Formalism.L2.Col.stdLat E n = Formalism.UG.stdLat (𝓞 E) := by
    ext y
    rw [Formalism.L2.Col.mem_stdLat, mem_stdLat_iff']
    rfl
  have e : Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) = Formalism.UG.stdLat (RInt F E) := by
    rw [e0]
    exact easyc_latS_std _ _
  rw [e, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact inv_mem ((afsplit_stab_iff _ k).2 ⟨h1, h2⟩) _

theorem emb_comm {v : HeightOneSpectrum (𝓞 F)} (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) {k : GL (Fin n) (AfE F E)}
    (hk : bc (prV (E := E) v) k = 1) : emb v x * k = k * emb v x := by
  have e : afsplitU v 1 k = k := by
    apply Units.ext
    rw [afsplitU_coe, ← hk, afsplit_coe_bc_prV, afsplitC_decomp]
  show afsplitU v x 1 * k = k * afsplitU v x 1
  rw [← e, ← afsplitU_mul, ← afsplitU_mul, one_mul, mul_one, one_mul, mul_one]

omit [StarRing E] in

abbrev StdAt (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  latS (F := F) (v.adicCompletion F) (intV E v) Lb = Formalism.UG.stdLat (intV E v)

theorem act_one {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (d : S.D b) :
    S.act b 1 d = d := one_smul _ _

end Small

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem reads_gLevH {B : Base} {X : PreX B.toPre} (I : TC B X) (hPr : (B.primes X).Ok) (u : B.Word)
    (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (i : ℕ) {Ch : Type} (chOf : (I.stp u I.mu0 i).Cl → Ch)
    {J : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E} (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (hbad : ∀ v ∈ bad, (B.host.g 0 : 𝓞 B.host.F) ∈ v.asIdeal ∨ (B.host.g 1 : 𝓞 B.host.F) ∈ v.asIdeal)
    (S : Ch → StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad) {y st k}
    (hR : I.Reads u I.mu0 i chOf (fun β => (S β).Lb) (fun β => (S β).U) (fun β => (S β).chi) y st k) (β : Ch) :
    ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)), (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal →
      Subgroup (GL (Fin (B.R.N i)) (kv B.host.F v))) (lam : ∀ j v h, H j v h →* ℂˣ), Nonempty (GLevH (S β) G H lam) := by
  subst hJ
  obtain ⟨c, rfl⟩ := hR.onto β
  have hT : ∀ j (v : HeightOneSpectrum (𝓞 B.host.F)), (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal → (B.T u : 𝓞 B.host.F) ∉ v.asIdeal := by
    intro j v h0 h1
    have hc : Nat.Coprime (B.T u) (B.host.g j) := (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime j)).2 (hPr.T_ne_g u j)
    obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 B.host.F))
    simp only [eq_intCast, Int.cast_natCast] at e
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h0)))
  have hL : ∀ j (v : HeightOneSpectrum (𝓞 B.host.F)), (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal →
      StdAt v (S (chOf c)).Lb := by
    intro j v h
    refine latS_eq_std (hT j v h) (fun x hx a => ?_) fun a => (hR.lb _ _).2 fun b => ?_
    · obtain ⟨r, hr, -⟩ := (hR.lb _ _).1 hx a
      exact ⟨r, hr⟩
    · by_cases e : b = a
      · subst e
        refine ⟨(B.T u : 𝓞 B.host.E), by rw [Pi.single_eq_same]; simp, fun _ => ⟨_, (hPr.piT_norm u).symm⟩⟩
      · exact ⟨0, by rw [Pi.single_eq_of_ne e]; simp, fun _ => dvd_zero _⟩
  refine exists_gLevH (S (chOf c)) G (fun j => (B.host.g_prime j).ne_zero)
    ((Nat.coprime_primes (B.host.g_prime 0) (B.host.g_prime 1)).2 B.host.g_ne) hbad hL fun j v h x hx => ?_
  have hk : bc (prV (E := B.host.E) v) (k (chOf c)) = 1 :=
    hR.k_off _ v (hT j v h) (fun ⟨P, hP, _⟩ => by rw [I.twistPrimes_reference_tuple_eq_empty] at hP; exact Finset.notMem_empty _ hP) (Or.inl rfl)
  have hp0 := (hR.pt c).of_extTo (I.Q_subset_SQ I.mu0) (by rw [I.twistPrimes_reference_tuple_eq_empty]; exact Finset.disjoint_empty_right _)
  have hxu : emb v x.1 ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) :=
    afsplitU_mem v _ _ _ _ x.2.1 (one_mem _)
  have hp1 := isPtOf_mul I.twistPrimes_reference_tuple_eq_empty hp0 hxu
    (afsplitC_int v _ _ (int_of_mem (hL j v h) x.2) (afsplit_one_mem _))
    (afsplitC_int v _ _ (int_of_mem (hL j v h) (x⁻¹).2) (afsplit_one_mem _))
    (val_emb_lt G j v h rfl (hL j v h) x hx)
  rw [mul_assoc, ← emb_comm _ hk, ← mul_assoc] at hp1
  have ha : (I.stp u I.mu0 i).act c.1 1 ((I.stp u I.mu0 i).rep c) = (I.stp u I.mu0 i).rep c := act_one _ _ _
  have hU : emb v x.1 ∈ (S (chOf c)).U := (hR.lev c _ _ hp1).2 ⟨1, map_one _, by rw [ha], by rw [ha]⟩
  refine ⟨hU, Units.ext ?_⟩
  have := hR.chr c ⟨_, hU⟩ 1 (map_one _) (by rw [ha]; exact hp1)
  rw [map_one, Units.val_one, map_one] at this
  exact this

set_option maxHeartbeats 1000000 in

theorem chart_gLevH {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (i : ℕ) (hi : i ≤ B.R.m)
    (Ch : Type) (chOf : (I.stp u I.mu0 i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi
      (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1)))
    (_hG : I.IdG l Z G) (hR : I.ReadsK l Z u I.mu0 i hi chOf K) (β : Ch) :
    ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
      Subgroup (GL (Fin (B.R.N i)) (kv (I.rec7 l Z).host.F v))) (lam : ∀ j v h, H j v h →* ℂˣ), Nonempty (GLevH (K β).lev G H lam) := by
  obtain ⟨k, hR⟩ := hR
  exact reads_gLevH I l.pr u G i chOf ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1 (fun v hv => hv) (fun β => (K β).lev) hR β

end GlobalTheory.Mem.Col2.ChartLevel

end
