import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsOfForallValuationRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.WeightBundle

theorem sum_pow_neg_val {o G : Type} [CommRing o] [IsDomain o] [AddCommGroup G] [Fintype G] {N : ℕ} [NeZero N]
    {w : o} (hw : IsPrimitiveRoot w N) (f : G →+ ZMod N) :
    ∑ a, w ^ (-(f a)).val = if f = 0 then (Fintype.card G : o) else 0 := by
  split_ifs with hf
  · simp [hf]
  · have h := AddChar.sum_eq_zero_of_ne_one
      (ψ := (AddChar.zmodChar N hw.pow_eq_one).compAddMonoidHom (-f)) (by
        intro h
        refine hf (AddMonoidHom.ext fun a => ?_)
        have h1 := DFunLike.congr_fun h a
        rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, AddChar.one_apply,
          hw.pow_eq_one_iff_dvd] at h1
        have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
        simpa using h2)
    simpa [AddChar.zmodChar_apply] using h

theorem nsmul_eq_zero_of_cast {r N : ℕ} [NeZero (r * N)] (x : ZMod (r * N))
    (h : ZMod.castHom (dvd_mul_left N r) (ZMod N) x = 0) : r • x = 0 := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at h
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_left r h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance neZero_N : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance neZero_rN : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne _)⟩

instance finite_hom (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) :=
  Finite.of_injective _ DFunLike.coe_injective

theorem isPrimitiveRoot_root : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))) (by ring)

theorem sum_proj [IsDomain o] (T : AddSubgroup S.Gam) (hT : S.IsoFree T) [Fintype (T →+ ZMod S.N)] :
    ∑ c, S.proj T c = 1 := by
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have hw := isPrimitiveRoot_root S
  have hu : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have key : ∀ t : T, ∑ c : T →+ ZMod S.N, S.ζN ^ (-(c t)).val • S.ρ t =
      (∑ c : T →+ ZMod S.N, S.ζN ^ (-(c t)).val) • (1 : Matrix S.J S.J o) := by
    intro t
    rw [← Finset.sum_smul]
    have h := sum_pow_neg_val hw (AddMonoidHom.eval t : (T →+ ZMod S.N) →+ ZMod S.N)
    simp only [AddMonoidHom.eval_apply_apply] at h
    split_ifs at h with h0
    · rw [S.ρ_one]
      have : S.r • e t = 0 := funext fun i => nsmul_eq_zero_of_cast _ (DFunLike.congr_fun h0
        ((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
          ((Pi.evalAddMonoidHom _ i).comp e.toAddMonoidHom)))
      rw [← map_nsmul, map_eq_zero_iff e e.injective] at this
      exact congrArg Subtype.val this
    · rw [h, zero_smul, zero_smul]
  simp only [ThetaSys.proj, finsum_eq_sum_of_fintype]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun t _ => key t, ← Finset.sum_smul,
    Finset.sum_comm, Finset.sum_congr rfl fun c _ => sum_pow_neg_val hw c, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [← Nat.card_eq_fintype_card, smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

variable (M : RatModel o Ω)

abbrev gens (z : M.Z) : Set (S.J → Ω) :=
  {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧
    x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}

theorem FF_mem (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k) : S.FF T c k ∈ S.R := by
  rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
  exact sum_mem fun t _ => mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem span_gens_eq [IsDomain o] {U₀ : M.Z.Opens} (hA : S.admitted M U₀) (z : M.Z) (hT : S.IsoFree (S.TT M z))
    (hF : ∀ c, S.FF (S.TT M z) c ≠ 0) {ξ : M.Z} (hξ : ξ ∈ U₀) :
    Submodule.span (M.O ξ) (gens S M z) =
      Submodule.span (M.O ξ) (Set.range fun i => Pi.single i (1 : Ω)) := by
  have hO : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξ
  have hR : S.R ≤ M.O ξ := hA.1.le.trans hO
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩
    refine (RatModel.Lat.mem_const_iff M).2 fun j => ?_
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hO (hA.1.FF_unit _ _ _ hT hk.1))) (Subalgebra.algebraMap_mem _ _)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨x₀, hx⟩ := hA.1.div z
    have := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
    have e : (Pi.single i (1 : Ω) : S.J → Ω) =
        ∑ c : S.TT M z →+ ZMod S.N, fun j => algebraMap o Ω (S.proj _ c j i) := by
      ext j
      rw [Finset.sum_apply, ← map_sum, ← Matrix.sum_apply, sum_proj S _ hT]
      simp [Matrix.one_apply, Pi.single_apply]
    show (Pi.single i (1 : Ω) : S.J → Ω) ∈ Submodule.span (M.O ξ) (gens S M z)
    rw [e]
    refine sum_mem fun c _ => ?_
    obtain ⟨k, hk⟩ := hA.2 _ c hT (hF c) z
    have hm : S.FF _ c k * (S.th x₀)⁻¹ ∈ M.O ξ := mul_mem (hR (FF_mem S _ _ _)) (hO (hA.1.th_unit _ hx.1))
    have e2 : (fun j => algebraMap o Ω (S.proj _ c j i)) = (⟨_, hm⟩ : M.O ξ) •
        fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i) := by
      ext j
      have h1 := hx.1
      have h2 := hk.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k, x₀, i, hk, hx, rfl⟩)

theorem exists_lat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → JacobsonSpace M.Z → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z : M.Z, ∃ (b : Matrix S.J S.J Ω) (W : M.Z.Opens), z ∈ W ∧ b.det ≠ 0 ∧ ∀ x ∈ W, Submodule.span (M.O x) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O x) (Set.range b)) → ∃ EE : M.Lat S.J, (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) ∧ ∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω)) := by
  intro o Ω _ _ _ hb S M U₀ hA hJ h0 hF hht hloc
  have := hb.ded
  choose b W hW hb0 hbW using hloc
  have hn := hA.1.normal
  obtain ⟨EE, h1, h2⟩ := GlobalTheory.ZH.exists_lat_of_height_le_one o Ω M hn S.J b
    (fun ξ => Submodule.span (M.O ξ) (gens S M ξ)) hb0 (by
      intro z hz
      have hfin := (GlobalTheory.ZH.normalModel_height_le_one o Ω M hn z).2.2 U₀ hA.1.ne
      have hfin' : {ξ : M.Z | (ξ ∉ U₀ ∧ ValuationRing (M.O ξ)) ∧ ¬ ξ ⤳ z}.Finite :=
        hfin.subset fun _ h => h.1
      have hcl : IsClosed (⋃ ξ ∈ {ξ : M.Z | (ξ ∉ U₀ ∧ ValuationRing (M.O ξ)) ∧ ¬ ξ ⤳ z}, closure {ξ}) :=
        hfin'.isClosed_biUnion fun _ _ => isClosed_closure
      refine ⟨W z ⊓ ⟨_, hcl.isOpen_compl⟩, ⟨hW z, ?_⟩, ?_⟩
      · intro h
        obtain ⟨ξ, hξ, h⟩ := Set.mem_iUnion₂.1 h
        exact hξ.2 (specializes_iff_mem_closure.2 h)
      · rintro ξ ⟨hξW, hξ⟩ hv
        rw [← hbW z ξ hξW]
        by_cases hU : ξ ∈ U₀
        · exact (span_gens_eq S M hA z (h0.1 z).1 (hF z) hU).trans
            (span_gens_eq S M hA ξ (h0.1 ξ).1 (hF ξ) hU).symm
        · refine hht z ξ hz ?_ hv
          by_contra hs
          exact hξ (Set.mem_iUnion₂.2 ⟨ξ, ⟨⟨hU, hv⟩, hs⟩, subset_closure rfl⟩))
  refine ⟨EE, fun z hz => (h1 z hz).trans (hbW z z (hW z)).symm, ?_⟩
  refine h2 U₀ (Matrix.of fun i => Pi.single i 1) ?_
    fun ξ hξ _ => span_gens_eq S M hA ξ (h0.1 ξ).1 (hF ξ) hξ
  have : (Matrix.of fun i => Pi.single i 1 : Matrix S.J S.J Ω) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.ZH.WeightBundle
