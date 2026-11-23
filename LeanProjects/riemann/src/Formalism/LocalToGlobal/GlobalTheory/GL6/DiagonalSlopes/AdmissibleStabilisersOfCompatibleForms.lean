import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem adms_int (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy : y ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)) (p q : Fin n) :
    ((((L.fr i v hv)⁻¹ * bc (G.phi i v hv) y * L.fr i v hv : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q) ∈ v.adicCompletionIntegers F := by
  classical
  set fr := L.fr i v hv
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) _) *ᵥ Pi.single q 1 with hw
  have hw' : ∀ b, (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) b ∈
      v.adicCompletionIntegers F := by
    intro b
    rw [hw, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    by_cases h : b = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  obtain ⟨y0, hy0, hy0w⟩ := (L.fr_lat i v hv w).2 hw'
  have hyy : (y : Matrix (Fin n) (Fin n) _) *ᵥ y0 ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := (hy y0).1 hy0
  have h1 := (L.fr_lat i v hv (fun b => G.phi i v hv (((y : Matrix (Fin n) (Fin n) _) *ᵥ y0) b))).1 ⟨_, hyy, fun b => rfl⟩ p
  have e1 : (fun b => G.phi i v hv (((y : Matrix (Fin n) (Fin n) _) *ᵥ y0) b)) =
      ((bc (G.phi i v hv) y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w := by
    have e2 : w = fun b => G.phi i v hv (y0 b) := funext fun b => (hy0w b).symm
    rw [e2]
    funext b
    exact (RingHom.map_mulVec (G.phi i v hv) (y : Matrix (Fin n) (Fin n) _) y0 b)
  rw [e1, mulVec_mulVec, hw, mulVec_mulVec] at h1
  have e3 : (((fr⁻¹ * bc (G.phi i v hv) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
      (Pi.single q (1 : v.adicCompletion F) : Fin n → v.adicCompletion F)) p = (((fr⁻¹ * bc (G.phi i v hv) y * fr : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) _) p q) := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← e3]
  simpa only [Units.val_mul, Matrix.mul_assoc] using h1

end Loc

section AdmsGL

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem adms_gl (v : HeightOneSpectrum (𝓞 F)) (M : GL (Fin n) (v.adicCompletion F))
    (hA : ∀ p q, (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈ v.adicCompletionIntegers F)
    (hB : ∀ p q, ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈
      v.adicCompletionIntegers F)
    (hU : ∀ p q : Fin n, (q < p → redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q = 0) ∧
      redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p p = 1) :
    M ∈ iwU F n v := by
  classical
  let A : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hA p q⟩
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hB p q⟩
  have hinj : ∀ P Q : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F),
      P.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
        Q.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) → P = Q := by
    intro P Q h
    funext p q
    exact Subtype.ext (congrFun (congrFun h p) q)
  have hAmap : A.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    funext p q; rfl
  have hBmap : B.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    funext p q; rfl
  have hAB : A * B = 1 := by
    apply hinj
    rw [Matrix.map_mul, hAmap, hBmap, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply hinj
    rw [Matrix.map_mul, hAmap, hBmap, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  let g0 : GL (Fin n) (v.adicCompletionIntegers F) := ⟨A, B, hAB, hBA⟩
  refine Subgroup.mem_map.2 ⟨g0, ?_, Units.ext hAmap⟩
  apply Subgroup.subset_closure
  intro p q
  have hred : ∀ p' q', ((redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g0 :
      GL (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) :
      Matrix (Fin n) (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) p' q' =
      (redM F v (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p' q' :
        (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
    intro p' q'
    simp only [redM]
    rw [dif_pos (hA p' q')]
    rfl
  exact ⟨fun hqp => by rw [hred]; exact (hU p q).1 hqp, by rw [hred]; exact (hU p p).2⟩

end AdmsGL

section Loc2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

set_option maxHeartbeats 1000000 in

theorem adms_iwU (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (ha : n ≤ a) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    (L.fr i v hv)⁻¹ * bc (G.phi i v hv) x * L.fr i v hv ∈ iwU F n v := by
  have hlev := S.Uloc_lev v hx
  have hI := (L.mem i v hv x hlev).1 hx
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := hlev.2
  have hinv : ((L.fr i v hv)⁻¹ * bc (G.phi i v hv) x * L.fr i v hv)⁻¹ =
      (L.fr i v hv)⁻¹ * bc (G.phi i v hv) x⁻¹ * L.fr i v hv := by
    rw [map_inv]; group
  refine adms_gl v _ (adms_int S G L i v hv x hst)
    (by rw [hinv]; exact adms_int S G L i v hv x⁻¹ ((stabGL _).inv_mem hst)) fun p q => ?_
  refine ⟨fun hqp => hI.1 p q ?_, hI.2.1 p (lt_of_lt_of_le p.2 ha)⟩
  simp only [blkOf, if_pos (lt_of_lt_of_le q.2 ha), if_pos (lt_of_lt_of_le p.2 ha)]
  exact hqp

end Loc2

section Tied

variable {D : D7} {u : D.what₂.Word}

theorem rank_zero_le_weight_count : D.R.N 0 ≤ D.R.k := by
  have := rank_eq_first_level D.R
  omega

set_option maxHeartbeats 2000000 in

theorem adms_core (Tf : Forms0 D u) (x : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (γ : GL (Fin (D.R.N 0)) D.host.E) (hγJ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ : x.1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * x.1 ∈
      (Tf.cls 0 (Nat.zero_le _) rfl).lev.U) : γ = 1 := by
  let _ := D.host.cmStar
  set S := (Tf.cls 0 (Nat.zero_le _) rfl).lev with hSdef
  choose vv hvv using fun i : Fin 2 => Formalism.L2.G.Triv.exists_place (F := D.host.F) (D.host.g i) (D.host.g_prime i)
  have hτ : ∀ τ : D.host.E →+* ℂ, τ.comp (sigD D : D.host.E →+* D.host.E) = (starRingEnd ℂ).comp τ :=
    fun τ => Formalism.L2.G.sig_conj D.sp.cm τ
  have hH : IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by
    have h := Formalism.L2.G.gram_herm D.sp.cm (D.sp.X 0)
    unfold IsHerm cT at h ⊢
    funext p q
    have h1 := congrFun (congrFun h ((finCongr (rankN D 0 (Nat.zero_le _))).symm p))
      ((finCongr (rankN D 0 (Nat.zero_le _))).symm q)
    simpa [gramN, sigD, Matrix.reindex_apply] using h1
  have hdet : IsUnit (gramN D 0 (Nat.zero_le _)).det := by
    have h := Formalism.L2.G.gram_det_unit D.sp.cm (D.sp.X 0)
    show IsUnit ((D.sp.X 0).gram.reindex _ _).det
    rw [Matrix.det_reindex_self]; exact h
  have hdef : IsTotDef (sigD D) (gramN D 0 (Nat.zero_le _)) :=
    Formalism.L2.G.Triv.totDef_reindex _ _ _
      (Formalism.L2.G.gram_totDef D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _)))
  exact Formalism.L2.G.Triv.gen_triv (sigD D) (gramN D 0 (Nat.zero_le _)) hτ hH hdet hdef S.Lb S.Lb_fin S.Lb_span S.U
    (fun x hx v => (S.Uloc_lev v (((S.U_eq x).1 hx).2 v)).2) D.host.g D.host.g_prime D.host.g_ne vv hvv
    (fun i => Tf.gl.phi i (vv i) (hvv i)) (fun i => (Tf.glev0).fr i (vv i) (hvv i))
    (fun i z hz => adms_iwU S Tf.gl (Tf.glev0) rank_zero_le_weight_count i (vv i) (hvv i) _ (((S.U_eq z).1 hz).2 (vv i)))
    x γ hγJ hγ

set_option maxHeartbeats 2000000 in

theorem adms_triv (Tf : Forms0 D u) (c : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
      (Tf.cls 0 (Nat.zero_le _) rfl).lev.U.map (MulAut.conj ((Tf.cls 0 (Nat.zero_le _) rfl).y c).1).toMonoidHom) :
    γ = 1 := by
  obtain ⟨κ, hκ, he⟩ := Subgroup.mem_map.1 hγ
  have hγ' : (((Tf.cls 0 (Nat.zero_le _) rfl).y c : UPts (sigD D) (gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _)⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * ((Tf.cls 0 (Nat.zero_le _) rfl).y c).1 ∈
        (Tf.cls 0 (Nat.zero_le _) rfl).lev.U := by
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
    exact hκ
  exact Subtype.ext (adms_core Tf _ γ.1 γ.2 hγ')

theorem admissible_stabilisers_of_compatible_forms (Tf : Forms0 D u) : Formalism.MainNotions.product_first_zeroth_parts.admS D u := by
  intro c
  have key : ∀ s : (D.mem u).C.stab 0 c, s = 1 := by
    intro s
    apply (Tf.cls 0 (Nat.zero_le _) rfl).stabI_inj c
    rw [map_one]
    exact adms_triv Tf c _ (((Tf.cls 0 (Nat.zero_le _) rfl).stabI_range c _).1 ⟨s, rfl⟩)
  exact ⟨fun a b => by rw [key a, key b]⟩

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0
