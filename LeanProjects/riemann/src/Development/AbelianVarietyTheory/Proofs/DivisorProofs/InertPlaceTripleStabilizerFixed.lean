import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximationStatement

noncomputable section

namespace GlobalTheory.ThK.UnifLevel

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.ConeEuler
open scoped TensorProduct Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def awayU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) : UA σ J →* UA σ J :=
  idemU σ J (1 - eFin v) (one_sub_idem (eFin_idem v))

theorem mat_awayU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    mat (awayU J v g) = (1 - eFin v) • mat g + (1 - (1 - eFin v)) • 1 := rfl

theorem compAt_mul_awayU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    compAt σ J v g * awayU J v g = g := by
  apply Subtype.ext; apply Units.ext
  change mat (compAt σ J v g) * mat (awayU J v g) = mat g
  rw [mat_compAt, mat_awayU, sub_sub_cancel]
  have h1 := idem_mul_one_sub (eFin_idem v)
  have h2 := one_sub_idem (eFin_idem v)
  have h3 := eFin_idem v
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, h1, h2, h3, mul_comm (1 - eFin v) (eFin v), zero_smul, add_zero, zero_add]
  have h4 : eFin v • mat g + (1 - eFin v) • mat g = mat g := by rw [← add_smul, add_sub_cancel, one_smul]
  first | exact h4 | (rw [add_comm]; exact h4)

theorem fstA_eFin (v : Pl F) : fstA F (eFin v) = 0 := rfl

theorem tmap_smul (a : AF F) (x : AE F E) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (a • x) =
      (fstA F a ⊗ₜ[F] (1 : E)) * Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

theorem awayU_mem_finU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) {k : UA σ J}
    (hk : k ∈ GlobalTheory.ThetaCplV.finU σ J) : awayU J v k ∈ GlobalTheory.ThetaCplV.finU σ J := by
  rw [GlobalTheory.ThetaCplV.mem_finU] at hk ⊢
  rw [← hk, mat_awayU]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, tmap_smul, map_sub, map_one, fstA_eFin,
    sub_zero, sub_self, Algebra.TensorProduct.one_def.symm, one_mul, TensorProduct.zero_tmul, zero_mul, add_zero]

theorem awayU_commute {n : ℕ} {X : Spc F E n} (v : Pl F) (k : UA σ X.J) {g : UA σ X.J}
    (hg : g ∈ UAt σ X (evFin F v)) : awayU X.J v k * g = g * awayU X.J v k := by
  set A := mat g - 1 with hAdef
  set C := mat k - 1 with hCdef
  have hA : (1 - eFin v) • A = 0 := hg _ (by rw [map_sub, map_one, eFin, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have e1 : mat g = A + 1 := by rw [hAdef, sub_add_cancel]
  have e2 : mat (awayU X.J v k) = (1 - eFin v) • C + 1 := by
    rw [mat_awayU, sub_sub_cancel, hCdef, smul_sub, sub_smul (1 : AF F) (eFin v) (1 : Matrix (Fin n) (Fin n) (AE F E)),
      one_smul]
    abel
  have h1 : A * ((1 - eFin v) • C) = 0 := by rw [Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]
  have h2 : ((1 - eFin v) • C) * A = 0 := by rw [Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero]
  have key : mat (awayU X.J v k) * mat g = mat g * mat (awayU X.J v k) := by
    rw [e1, e2]
    simp only [add_mul, mul_add, one_mul, mul_one, h1, h2]
    abel
  apply Subtype.ext; apply Units.ext
  exact key

theorem continuous_idemU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : AF F) (hε : ε * ε = ε) :
    Continuous (idemU σ J ε hε) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hm : Continuous fun g : UA σ J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ J => mat g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun g : UA σ J => ε • mat g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))
    exact (hm.const_smul ε).add continuous_const
  · change Continuous fun g : UA σ J => ε • mat g⁻¹ + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))
    exact (hmi.const_smul ε).add continuous_const

theorem om_mul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (g h : UA σ W.J) (Φ : Fn F n d) :
    om (1, g * h) Φ = om (1, g) (om (1, h) Φ) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem exists_level (hK : KP) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W}
    {χX χW : Chr F E} {om : Rep σ Y W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧
      ∀ k ∈ U, k ∈ GlobalTheory.ThetaCplV.finU σ W.J → om (1, k) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, -, φ, hSB, hev, rfl⟩ := hx
    obtain ⟨U, hU, h⟩ := GlobalTheory.T.exists_open_subgroup_fixing_pure_tensor F E σ B n d Y W M χX χW om _ _ _ _ hK hP f φ hSB hev
    exact ⟨U, hU, fun k hk hf => h k hk (GlobalTheory.ThetaCplV.mem_finU.1 hf)⟩
  | zero => exact ⟨⊤, isOpen_univ, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hf => by rw [map_add, h k hk.1 hf, h' k hk.2 hf]⟩
  | smul t x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hf => by rw [map_smul, h k hk hf]⟩

theorem level_of_span_at : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)),
    (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v)) →
    (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ O ∧
      ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) → g ∈ K) →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ U : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), IsOpen (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) ∧
      ∀ Ψ ∈ Submodule.span ℂ (Set.range fun g : GlobalTheory.ThK.UAtSub σ G.W (GlobalTheory.AdelicU.evFin F v) => om (1, g.1) Φ),
        (∀ k ∈ K, om (1, k) Ψ = Ψ) → ∀ k ∈ U, k ∈ GlobalTheory.ThetaCplV.finU σ G.W.J → om (1, k) Ψ = Ψ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT v K hKv hO Φ hΦ
  obtain ⟨O, hOo, hO1, hOK⟩ := hO
  obtain ⟨UΦ, hUΦ, hfix⟩ := exists_level hKP (GlobalTheory.ThK.Inhab.pairV hT) hΦ
  set cv := compAt σ G.W.J v with hcv
  set cw := awayU (σ := σ) G.W.J v with hcw
  let U : Subgroup (UA σ G.W.J) := K.comap cv ⊓ UΦ.comap cw
  have hS : IsOpen (cv ⁻¹' O ∩ cw ⁻¹' (UΦ : Set (UA σ G.W.J))) :=
    (hOo.preimage (continuous_idemU _ _ _)).inter (hUΦ.preimage (continuous_idemU _ _ _))
  have hSU : cv ⁻¹' O ∩ cw ⁻¹' (UΦ : Set (UA σ G.W.J)) ⊆ (U : Set (UA σ G.W.J)) := by
    rintro k ⟨h1, h2⟩
    exact ⟨hOK _ h1 (compAt_mem v k), h2⟩
  have h1S : (1 : UA σ G.W.J) ∈ cv ⁻¹' O ∩ cw ⁻¹' (UΦ : Set (UA σ G.W.J)) :=
    ⟨by simpa [map_one] using hO1, by simp [map_one]⟩
  refine ⟨U, Subgroup.isOpen_of_mem_nhds U (Filter.mem_of_superset (hS.mem_nhds h1S) hSU), ?_⟩
  intro Ψ hΨ hΨK k hk hkf
  have hw : om (1, cw k) Ψ = Ψ := by
    clear hΨK
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [← om_mul, awayU_commute v k g.2, om_mul, hfix _ hk.2 (awayU_mem_finU _ v hkf)]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul t x _ hx => rw [map_smul, hx]
  conv_lhs => rw [← compAt_mul_awayU G.W.J v k]
  rw [om_mul, hw]
  exact hΨK _ hk.1

end GlobalTheory.ThK.UnifLevel
