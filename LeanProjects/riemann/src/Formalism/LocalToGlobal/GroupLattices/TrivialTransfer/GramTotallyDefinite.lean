import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsStab
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GenCoprime
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Triv

open Formalism.L2.G.Cmp

section Reindex

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [NumberField F] [Algebra F E] [DecidableEq n] [DecidableEq m] [Field F] in
theorem hform_reindex (e : n ≃ m) (σ : E →+* E) (J : Matrix n n E) (x y : m → E) :
    hform σ (J.reindex e e) x y = hform σ J (x ∘ e) (y ∘ e) := by
  simp only [hform, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  exact Fintype.sum_equiv e.symm _ _ fun i => Fintype.sum_equiv e.symm _ _ fun j => by simp

omit [DecidableEq n] [DecidableEq m] in
theorem totDef_reindex (e : n ≃ m) (σ : E →ₐ[F] E) (J : Matrix n n E) (h : IsTotDef σ J) : IsTotDef σ (J.reindex e e) := by
  refine ⟨h.1, fun ι => ?_⟩
  have hne : ∀ x : m → E, x ≠ 0 → x ∘ e ≠ 0 := fun x hx h0 =>
    hx (funext fun i => by simpa using congrFun h0 (e.symm i))
  have h2 := h.2 ι
  unfold IsDefiniteAt at h2 ⊢
  rcases h2 with h2 | h2
  · left
    intro x hx
    obtain ⟨a, ha, hpos⟩ := h2 (x ∘ e) (hne x hx)
    exact ⟨a, by rw [hform_reindex]; exact ha, hpos⟩
  · right
    intro x hx
    obtain ⟨a, ha, hpos⟩ := h2 (x ∘ e) (hne x hx)
    exact ⟨a, by rw [hform_reindex]; exact ha, hpos⟩

end Reindex

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem gram_totally_definite (sp : Spaces R F E) : IsTotDef sp.cm.sig sp.gram0 :=
  totDef_reindex _ _ _ (gram_totDef sp.cm (sp.X 0) (sp.X_sig 0) (sp.X_def 0 (Nat.zero_le _)))

theorem U_stab (L : ColLevel R F E sp gp C A clsLat) (x : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ L.U)
    (v : HeightOneSpectrum (𝓞 F)) :
    bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) L.Lb) :=
  (Subgroup.mem_inf.1 (L.Uloc_lev v (((L.U_eq x).1 hx).2 v))).2

theorem trivStabU (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) : TrivStabU L := by
  intro x γ hγ
  choose v hv using fun i => exists_place (F := F) (gp i) (hp i)
  apply Subtype.ext
  exact gen_triv sp.cm.sig sp.gram0 (sig_conj sp.cm) sp.baseGram_isHermitian (isUnit_det_gram0 sp) (gram_totally_definite sp)
    L.Lb L.Lb_fin L.Lb_span L.U (fun z hz w => U_stab L z hz w) gp hp hne v hv
    (fun i => (RingHom.fst _ _).comp (L.splitG i (v i) (hv i)).toRingHom)
    (fun i => L.frG i (v i) (hv i))
    (fun i z hz => (L.Uloc_g i (v i) (hv i) _ (L.Uloc_le (v i) (((L.U_eq z).1 hz).2 (v i)))).1
      (((L.U_eq z).1 hz).2 (v i)))
    x γ γ.2 (Subgroup.mem_subgroupOf.1 hγ)

theorem card_stab (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) (c : C.cls 0) :
    Nat.card (C.stab 0 c) = 1 := by
  rw [Nat.card_congr (stabRec (L := L) c)]
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, ?_⟩⟩⟩
  · exact (trivStabU L hp hne _ _ a.2).trans (trivStabU L hp hne _ _ b.2).symm
  · rw [map_one, mul_one, inv_mul_cancel]
    exact one_mem _

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trivStabU_rec (D : D7) (lev : LevelData D) (u : D.what₂.Word) : TrivStabU (lev u) :=
  trivStabU (lev u) D.host.g_prime D.host.g_ne

theorem stabZero_rec (D : D7) (lev : LevelData D) (u : D.what₂.Word) : (D.mem u).C.StabZero := fun c =>
  (Nat.card_eq_one_iff_unique.1 (card_stab (lev u) D.host.g_prime D.host.g_ne c)).1

end Record

end Formalism.L2.G.Triv

end
