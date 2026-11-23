import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicElementPlaceFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenPlacesStableStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTruncAct

open GlobalTheory.TruncFix
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem truncMat_mul_sub {n : ℕ} (e : AF F) {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : B * A = 1) :
    truncMat e B * A - 1 = (1 - e) • (A - 1) := by
  simp only [truncMat, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_mul, h]
  module

theorem mul_truncMat_sub {n : ℕ} (e : AF F) {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : B * A = 1) :
    B * truncMat e A - 1 = (1 - e) • (B - 1) := by
  simp only [truncMat, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub, h]
  module

theorem mat_compl {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (S : Finset (Pl F)) (l : UA σ J) :
    mat ((truncU S l)⁻¹ * l) - 1 = (1 - idem S) • (mat l - 1) := by
  rw [show mat ((truncU S l)⁻¹ * l) = mat (truncU S l)⁻¹ * mat l from rfl, mat_truncU_inv]
  exact truncMat_mul_sub _ (Units.inv_mul l.1)

theorem mat_compl_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (S : Finset (Pl F)) (l : UA σ J) :
    mat ((truncU S l)⁻¹ * l)⁻¹ - 1 = (1 - idem S) • (mat l⁻¹ - 1) := by
  rw [mul_inv_rev, inv_inv, show mat (l⁻¹ * truncU S l) = mat l⁻¹ * mat (truncU S l) from rfl, mat_truncU]
  exact mul_truncMat_sub _ (Units.inv_mul l.1)

theorem snd_eq_zero {a : AF F} (h : At (evI F) a) : a.2 = 0 := by
  have h0 : evI F ((0 : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) = 0 := map_zero _
  have h1 := congrArg Prod.snd (h _ h0)
  change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * a.2 = 0 at h1
  rwa [one_mul] at h1

theorem mul_one_sub_idem {S : Finset (Pl F)} {w : Pl F} (hw : w ∈ S) {u : AF F} (hu : At (evFin F w) u) :
    u * (1 - idem S) = 0 := by
  classical
  have h := hu (1 - idem S) (by rw [map_sub, map_one, evFin_idem, if_pos hw, sub_self])
  rwa [smul_eq_mul, mul_comm] at h

theorem lat_compl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {S : Finset (Pl F)} {w : Pl F} (hw : w ∉ S) (l : UA σ Y.J)
    (hl : ∀ γ, γ * (mat l)ᵀ ∈ latAtV X Y w ↔ γ ∈ latAtV X Y w) (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    γ * (mat ((truncU S l)⁻¹ * l))ᵀ ∈ latAtV X Y w ↔ γ ∈ latAtV X Y w := by
  have hs : (1 - idem S) * GlobalTheory.UnitaryPlaceSplit.idemAt w = GlobalTheory.UnitaryPlaceSplit.idemAt w := by
    have h0 : GlobalTheory.UnitaryPlaceSplit.idemAt w * idem S = 0 := liftV_mul_idem hw
    rw [sub_mul, one_mul, mul_comm, h0, sub_zero]
  refine GlobalTheory.AdelicPlaceDecomp.mul_transpose_mem_iff X Y w hs (mat_compl S l) (mat_compl_inv S l)
    (Units.inv_mul ((truncU S l)⁻¹ * l).1) (fun δ hδ => (hl δ).2 hδ) (fun δ hδ => (hl _).1 ?_) γ
  have h1 : mat l * mat l⁻¹ = 1 := Units.mul_inv l.1
  rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.mul_one]

theorem act_eq_trunc : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), S₁ ⊆ S → ∀ l : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, l ∈ GlobalTheory.ThKAdm.FinPt σ G.W → (∀ (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (γ : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (γ' : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), (γ * Matrix.transpose (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat l) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧ (γ' * Matrix.transpose (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat l) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w)) → om' (1, l) Ψ = om' (1, GlobalTheory.TruncFix.truncU S l) Ψ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT Ψ hΨ
  classical
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.compact_open_places_stable hKP F E σ B a a' G X om om' hT
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, -, φ, hSB, hvac, rfl⟩ := hx
    have hfin := Filter.eventually_cofinite.1 hvac
    refine ⟨S₀ ∪ hfin.toFinset, fun S hS l hl hlat => ?_⟩
    have hfix := (hS₀ S hfin.toFinset ((truncU S l)⁻¹ * l) (Finset.subset_union_left.trans hS)
      (Finset.subset_union_right.trans hS)
      (fun u hu => by
        rw [mat_compl, smul_comm, hl u (snd_eq_zero hu), smul_zero])
      (fun w hw u hu => by
        rw [mat_compl, smul_smul, mul_one_sub_idem hw hu, zero_smul])
      (fun w hw => lat_compl G.V G.W hw l fun γ => (hlat w γ 0).1)
      (fun w hw => lat_compl G.V' G.W hw l fun γ => (hlat w 0 γ).2)).2 f φ hSB
      (fun w hw => by_contra fun h => hw (hfin.mem_toFinset.2 h))
    conv_rhs => rw [← hfix]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_inv_cancel_left]
  | zero => exact ⟨∅, fun S _ l _ _ => by rw [map_zero, map_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨S₁, h₁⟩ := ihx
    obtain ⟨S₂, h₂⟩ := ihy
    refine ⟨S₁ ∪ S₂, fun S hS l hl hlat => ?_⟩
    rw [map_add, map_add, h₁ S (Finset.subset_union_left.trans hS) l hl hlat,
      h₂ S (Finset.subset_union_right.trans hS) l hl hlat]
  | smul c x _ ih =>
    obtain ⟨S₁, h₁⟩ := ih
    exact ⟨S₁, fun S hS l hl hlat => by rw [map_smul, map_smul, h₁ S hS l hl hlat]⟩

end GlobalTheory.ThKTruncAct

end
