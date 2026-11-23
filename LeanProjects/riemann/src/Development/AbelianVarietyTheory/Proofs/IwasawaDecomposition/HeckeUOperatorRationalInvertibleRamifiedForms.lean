import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumPairsAboveEqAffineHyperplaneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfUpSumOfNormStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLocalPairMapAdelicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownwardLevelMoveReachesKernelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpecStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorMemAdelicFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamondStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationalityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjectiveStatement

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.Main

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem eq_zero_of_reps (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S))) (g) (hg : g ∈ AdFun S emb)
    (h0 : ∀ c, g (y c) = 0) (x : GA σ J) : g x = 0 := by
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
  obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ (y c) x).1 hc
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 ha
  funext s
  obtain ⟨s', hs'⟩ := exists_isTr' emb γ s
  have := hg γ hγ (y c) x ⟨b.1, Subgroup.mem_subgroupOf.1 hb⟩ (by rw [hab, e]; rfl) s s' hs'
  rw [this, h0 c]; simp

theorem pair_move {S : StepLevel F E σ J T f bad} {v : HeightOneSpectrum (𝓞 F)} {hv : (T : 𝓞 F) ∈ v.asIdeal}
    {k : Type} [Field k] {p : GA σ J → Pr (𝓞 E) (Fin n → E) k} (hp : PMap S v hv p)
    (γ : UJ (σ : E →+* E) J) (y y' η : GA σ J) (κ : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 * y'.1 = y.1 * η.1 * κ.1) :
    p (y * η) = (p y').act (glE γ.1) := by
  have hκ := (S.U_eq _).1 κ.2
  rw [← (hp.2.1 (y * η) ⟨κ.1, hκ.1⟩).2 (hκ.2 v)]
  exact hp.1 γ.1 γ.2 y' _ h.symm

end Gen

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def rs (g : GA (sigD D) (gramN D 0 (Nat.zero_le _)) → Fr D 0 (Nat.zero_le _) → ℂ) : LT.Fn D u 0 :=
  fun c s => g (T.cls0.y c) (T.val0.eY s)

include T in
theorem herm : cT (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) = gramN D 0 (Nat.zero_le _) := by
  obtain ⟨C, hC, -⟩ := T.val0.de
  have hσσ : ∀ x, sigD D (sigD D x) = x := fun x => by rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]
  rw [← hC]
  ext a b
  simp [cT, Matrix.mul_apply, hσσ, mul_comm]

theorem mem_Fi (φ : LT.Fn D u 0) : φ ∈ (D.fm u).Fi 0 ↔ ∃ g ∈ AdForms T.cls0.lev (embT D) (lamT u 0), rs T g = φ := by
  rw [T.val0.Fi]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, ?_⟩
    funext c z
    have := congrFun (congrFun h c) (T.val0.eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, hg, ?_⟩
    funext c z
    show g _ z = g _ (T.val0.eY (T.val0.eY.symm z))
    rw [Equiv.apply_symm_apply]

theorem zero_of_rs (g) (hg : g ∈ AdFun T.cls0.lev (embT D)) (h : rs T g = 0) (x) : g x = 0 := by
  refine eq_zero_of_reps _ _ T.cls0.y T.cls0.y_bij.2 g hg (fun c => ?_) x
  funext s
  have := congrFun (congrFun h c) (T.val0.eY.symm s)
  simpa [rs] using this

theorem exists_dia (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ (k : ℤ) (δ : GA (sigD D) (gramN D 0 (Nat.zero_le _))), (k : (D.mem u).A.Fv v) = a ∧
      IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ := by
  obtain ⟨k, hk, hkT⟩ := unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := splitAtT_of_tied T.atT v
  obtain ⟨δ, hδ⟩ := is_diamond_of_local_diamond _ _ _ k
    (local_diamond_of_split_idempotent T.cls0.lev _ (T.atT.eV v).2 (D.mem u).A.T_prime k hkT e he hee hσ)
  exact ⟨k, δ, hk, hδ⟩

theorem torsionFree (x : Fin (D.R.N 0) → D.host.E) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x = 0) : x = 0 := by
  rw [Nat.cast_smul_eq_nsmul] at h
  exact (smul_eq_zero.1 h).resolve_left (D.mem u).A.T_prime.ne_zero

variable (v : (D.mem u).A.vT)
  (p : GA (sigD D) (gramN D 0 (Nat.zero_le _)) → Pr (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E) ((D.mem u).A.Fv v))
  (hp : PMap T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 p) (hy : ∀ c, p (T.cls0.y c) = pc T.lv0 v c)

include hp hy

set_option maxHeartbeats 2000000 in

theorem uop_rs (g) (hg : g ∈ AdFun T.cls0.lev (embT D)) :
    LT.Uop D u 0 v (rs T g) = rs T (upAd (T.atT.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (T.atT.eV v).1 p g) := by
  classical
  funext c
  have hun := GlobalTheory.T.levelPrime_unramifiedUniformizer D u T.atT v
  have key : ∀ w : (D.fm u).lv 0 v c, (D.fm u).fv 0 v c w = 1 → ∃ η : GA (sigD D) (gramN D 0 (Nat.zero_le _)),
      AtV (T.atT.eV v).1 η ∧ ((p (T.cls0.y c * η)).Ok (T.atT.res v) ∧ (p (T.cls0.y c * η)).IsKer (pc T.lv0 v c).L ∧
        ∃ e, (p (T.cls0.y c * η)).f e = 1 ∧ locExt (T.atT.res v) (Ld D u 0 (Nat.zero_le _) c) (T.lv0.pr v c)
          ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = w) ∧
      (D.fm u).upT 0 v c w (rs T g ((D.fm u).up 0 v c w)) = fun s => g (T.cls0.y c * η) (T.val0.eY s) := by
    intro w hw
    obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c w
    obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := T.up_natural_level_zero.upTie v c z hw
    refine ⟨η, h1, ?_, h6 g hg⟩
    rw [pair_move hp γ _ _ η κ h2, hy]
    exact ⟨(pc_ok _ _ _).act _, GlobalTheory.T.upwardLevelMove_incidence_of_pairs D u T.atT 0 _ T.lv0 T.cls0 v c _ z γ.1 hw h3 h4 h5⟩
  choose! η h1 h2 h3 using key
  have hsum := GlobalTheory.T.finsum_pairsAbove_eq_affineHyperplane _ _ _ _ _ (T.atT.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (pc T.lv0 v c)
    (locExt (T.atT.res v) (Ld D u 0 (Nat.zero_le _) c) (T.lv0.pr v c)) ((D.fm u).fv 0 v c)
    (fun w => p (T.cls0.y c * η w)) (valAt (T.atT.eV v).1 p g (T.cls0.y c)) (T.atT.res_surj v) hun.1 torsionFree
    (pc_ok T.lv0 v c).sat
    (locExt_red _ _ hun _ _ (T.lv0.pr_smul v c) (T.lv0.pr_surj v c) (T.lv0.pr_ker v c)) (fun _ _ => rfl) h2
  have hval := (GlobalTheory.T.adelicForm_values_near_point_spec _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p (level_places_not_bad T.atT v) hp g hg).1
  funext s
  show _ = upAd _ _ _ p g (T.cls0.y c) (T.val0.eY s)
  unfold upAd
  rw [hy, hsum, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_apply]
  simp only [LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  refine Finset.sum_congr (by ext w; simp) fun w hw => ?_
  have hw' : (D.fm u).fv 0 v c w = 1 := by simpa using hw
  rw [h3 w hw', hval _ _ (h1 w hw')]

theorem uop_mem (φ : LT.Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) : LT.Uop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  obtain ⟨g, hg, rfl⟩ := (mem_Fi T φ).1 hφ
  rw [uop_rs T v p hp hy g hg.1, mem_Fi T]
  exact ⟨_, GlobalTheory.T.upwardOperator_mem_adelicForms _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p (level_places_not_bad T.atT v) hp _ _ _ g hg, rfl⟩

set_option maxHeartbeats 1000000 in
theorem uop_rho (hok : ∀ x, (p x).Ok (T.atT.res v)) (φ : LT.Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) (v' : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v')ˣ) :
    (D.mem u).A.rhoT v' a (LT.Uop D u 0 v φ) = LT.Uop D u 0 v ((D.mem u).A.rhoT v' a φ) := by
  obtain ⟨g, hg, rfl⟩ := (mem_Fi T φ).1 hφ
  obtain ⟨k, δ, hk, hδ⟩ := exists_dia T v' a
  have hU := GlobalTheory.T.upwardOperator_mem_adelicForms _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p (level_places_not_bad T.atT v) hp
    (T.atT.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) _ g hg
  have e1 : (D.mem u).A.rhoT v' a (rs T g) = rs T (fun x => g (x * δ)) := rhoT_eq T.val0 v' a k hk δ hδ g hg.1
  rw [e1, uop_rs T v p hp hy g hg.1,
    uop_rs T v p hp hy _ (adelic_function_right_translate_diamond _ _ _ _ (level_places_not_bad T.atT v') hδ hg.1)]
  refine (rhoT_eq T.val0 v' a k hk δ hδ _ hU.1).trans ?_
  funext c s
  have hne : (T.atT.eV v').1 = (T.atT.eV v).1 → (k : (D.mem u).A.Fv v) ≠ 0 := by
    intro h
    obtain rfl : v' = v := T.atT.eV.injective (Subtype.ext h)
    rw [hk]; exact a.ne_zero
  exact (congrFun (GlobalTheory.T.upwardHeckeOperator_commute_diamond _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p (level_places_not_bad T.atT v) hp
    (T.atT.res v) _ (T.atT.res_surj v) hok g hg.1 _ (T.atT.eV v').2 k δ (level_places_not_bad T.atT v') hne hδ _) _).symm

theorem uop_ram (hok : ∀ x, (p x).Ok (T.atT.res v)) (φ : LT.Fn D u 0) (hφ : φ ∈ (D.mem u).A.Mram) : LT.Uop D u 0 v φ ∈ (D.mem u).A.Mram := by
  have h1 : φ ∈ (D.fm u).Fi 0 := by rw [(D.fm u).Fi_zero]; exact hφ.1
  refine ⟨by rw [← (D.fm u).Fi_zero]; exact uop_mem T v p hp hy φ h1, (Submodule.mem_iInf _).2 fun v' => ?_⟩
  have h2 : (D.mem u).A.Nm v' φ = 0 := (Submodule.mem_iInf _).1 hφ.2 v'
  show (D.mem u).A.Nm v' _ = 0
  unfold ColumnsAtT.Nm at h2 ⊢
  rw [LinearMap.sum_apply] at h2 ⊢
  rw [Finset.sum_congr rfl (fun a _ => uop_rho T v p hp hy hok φ h1 v' a), ← map_sum, h2, map_zero]

set_option maxHeartbeats 2000000 in
theorem uop_inj (φ : LT.Fn D u 0) (hφ : φ ∈ (D.mem u).A.Mram) (h0 : LT.Uop D u 0 v φ = 0) : φ = 0 := by
  classical
  have h1 : φ ∈ (D.fm u).Fi 0 := by rw [(D.fm u).Fi_zero]; exact hφ.1
  have h2 : (D.mem u).A.Nm v φ = 0 := (Submodule.mem_iInf _).1 hφ.2 v
  obtain ⟨g, hg, rfl⟩ := (mem_Fi T φ).1 h1
  have hun := GlobalTheory.T.levelPrime_unramifiedUniformizer D u T.atT v
  have hb := level_places_not_bad T.atT v
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.T.adelicForm_values_near_point_spec _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p hb hp g hg.1
  have hU := GlobalTheory.T.upwardOperator_mem_adelicForms _ _ _ _ _ _ _ _ _ T.cls0.lev (embT D) _ (T.atT.eV v).2 _ p hb hp
    (T.atT.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) _ g hg
  rw [uop_rs T v p hp hy g hg.1] at h0
  have hU0 := zero_of_rs T _ hU.1 h0
  choose k δ hk hδ using exists_dia T v
  have hN : ∀ x, ∑ a, g (x * δ a) = 0 := by
    intro x
    have hm : (∑ a, fun x => g (x * δ a)) ∈ AdFun T.cls0.lev (embT D) :=
      Submodule.sum_mem _ fun a _ => adelic_function_right_translate_diamond _ _ _ _ hb (hδ a) hg.1
    have := zero_of_rs T _ hm (by
      rw [← h2]
      unfold ColumnsAtT.Nm
      have e : ∀ a, (D.mem u).A.rhoT v a (rs T g) = rs T (fun x => g (x * δ a)) :=
        fun a => rhoT_eq T.val0 v a (k a) (hk a) (δ a) (hδ a) g hg.1
      rw [LinearMap.sum_apply, Finset.sum_congr rfl (fun a _ => e a)]
      funext c s
      simp only [rs, Finset.sum_apply]) x
    rwa [Finset.sum_apply] at this
  funext c
  haveI : Module.Finite ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) :=
    Module.finite_of_finrank_pos (by rw [(D.fm u).lk_rank]; exact D.R.N_pos 0)
  haveI : Finite ((D.fm u).lk 0 v c) := Module.finite_of_finite ((D.mem u).A.Fv v)
  have hinj := GlobalTheory.T.eq_zero_of_sum_inc_eq_zero_of_sum_dil_eq_zero _ _ _ _ _ (T.atT.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E)
    (loc (T.atT.res v) (Lk T.atT 0 (Nat.zero_le _) v c))
    (locExt (T.atT.res v) (Lk T.atT 0 (Nat.zero_le _) v c) (T.lv0.prk v c)) (valAt (T.atT.eV v).1 p g (T.cls0.y c))
    (T.atT.res_surj v) hun.1 torsionFree (loc_sat _ _)
    (locExt_red _ _ hun _ _ (T.lv0.prk_smul v c) (T.lv0.prk_surj v c) (T.lv0.prk_ker v c))
    (fun g' hg' => by
      obtain ⟨γ, η, κ, e1, e2, e3, e4, -⟩ := T.down_natural_level_zero v c g' hg'
      obtain ⟨f1, f2⟩ := GlobalTheory.T.downwardLevelMove_reaches_kernelLattice D u T.atT 0 _ T.lv0 T.cls0 v c _ g' γ.1 e3 e4
      have hm := pair_move hp γ _ _ η κ e2
      rw [hy] at hm
      refine ⟨_, f1, f2, ?_⟩
      have := hU0 (T.cls0.y c * η)
      unfold upAd at this
      rwa [hm, hv2 _ _ e1] at this)
    (fun q _ _ => by
      have e : ∀ a : ((D.mem u).A.Fv v)ˣ, valAt (T.atT.eV v).1 p g (T.cls0.y c) (q.dil (a : (D.mem u).A.Fv v)) =
          valAt (T.atT.eV v).1 p (fun y => g (y * δ a)) (T.cls0.y c) q := fun a => by
        rw [← hk a]; exact hv3 (k a) (δ a) _ q (by rw [hk a]; exact a.ne_zero) (hδ a)
      rw [Finset.sum_congr rfl (fun a _ => e a)]
      unfold valAt
      split_ifs with h
      · exact hN _
      · simp)
    (pc T.lv0 v c) (pc_ok _ _ _) (pc_isKer T.lv0 T.cls0 v c)
  have h3 := hv1 (T.cls0.y c) 1 (fun v' _ => map_one _)
  rw [mul_one, hy, hinj] at h3
  funext s
  show g _ _ = 0
  rw [← h3]; rfl

end GlobalTheory.LevelHecke.Main

namespace GlobalTheory.LevelHecke

open Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

theorem commensurable_of_tied (D : D7) (u : D.what₂.Word) (T : Forms0 D u)
    (h : ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) (w : D.what₂.places.Pl) :
    ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
      ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  choose p hp hy hok using GlobalTheory.T.exists_equivariant_local_pair_map_adelic D u T.atT 0 _ T.lv0 T.cls0 T.fMe0 T.fv0 (Main.herm T)
  refine GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective D u (fun v x hx => ?_) (fun v φ hφ => Main.uop_inj T v (p v) (hp v) (hy v) φ hφ) w
  have h1 := Main.uop_ram T v (p v) (hp v) (hy v) (hok v) _ hx
  obtain ⟨y, hy'⟩ := GlobalTheory.T.upwardOperator_preserves_rationality D u T h v x (by rw [(D.fm u).Fi_zero]; exact h1.1)
  exact ⟨y, by show (D.fm u).emb 0 y ∈ (D.mem u).A.Mram; rw [hy']; exact h1, hy'⟩

theorem commensurable_at_level : ∀ (X : Stages), Nonempty (PreX X.B.toPre) → ∀ (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Formalism.L2.Forms.Forms0 X.toD7 u), (∀ u, Formalism.L2.Forms.Joint0 H.base.lev0 u (T u)) → (∀ u i v h x, ∃ r : X.B.LL, X.B.embLL r = (T u).gl.psi0 i v h x) → ∀ u (w : X.toD7.what₂.places.Pl), X.toD7.what₂.places.resChar w = (X.toD7.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL X.toD7 u, X.toD7.nuIn u (n • x) ∈ LT.Nlam X.toD7 u w) ∧ ∀ x, X.toD7.nuIn u x ∈ LT.Nlam X.toD7 u w → InLoc (X.toD7.plEq w) (DV.MramL X.toD7 u) (n • x) :=
  fun X _ _ T _ h u w _ => commensurable_of_tied X.toD7 u (T u) (h u) w

end GlobalTheory.LevelHecke

end
