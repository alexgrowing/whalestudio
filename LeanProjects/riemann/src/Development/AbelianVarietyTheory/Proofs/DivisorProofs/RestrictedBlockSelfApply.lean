import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodFormsSpanInduced
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CarriedGeneratorUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent

noncomputable section

namespace GlobalTheory.LevelSpanCompare

section Move

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem reflects_half_of_move {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : IsLevMove ρ ν gM gA) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (b : KA l →+* k)
    (hx : x ≫ Xo.s = spMap b) (a : Dw.La) (ha : gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨hs, hM, -⟩ := h
  obtain ⟨-, J, -, -, hJM⟩ := Xo.univ.geom k (x ≫ ρ) b (by rw [Category.assoc, hs]; exact hx)
  have h1 : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime]; simp
  rw [Submodule.sup_smul] at h1
  obtain ⟨b, hb, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
  have hgb : gM b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := gM) hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hga : gM a' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.sub_mem _ ha hgb
    simpa using this
  have e1 : ρ ≫ (Xo.univ.eta a').left = ρ ≫ (Xo.univ.eta 0).left := by
    rw [← hM a', ← hM 0, Xo.univ.eta_ker _ hga, Xo.univ.eta_ker (gM 0) (by simp)]
  have e5 : J.ev l.M a' = J.ev l.M 0 := by
    rw [← hJM _ ha', ← hJM _ (Submodule.zero_mem _)]
    ext
    simpa using congrArg (x ≫ ·) e1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have e6 : J.ev l.M 0 = 1 := (J.ker l.M hM0 0).2 ⟨0, by simp⟩
  obtain ⟨b', hb'⟩ := (J.ker l.M hM0 a').1 (e5.trans e6)
  refine Submodule.add_mem _ hb ?_
  rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (GlobalTheory.LevelGroupTest.natCast_mem_half l) trivial

theorem levR_unique (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (gM : Dw.La →ₗ[𝓞 E] Dw.La)
    {S : Type} [CommRing S] [Algebra c.F S] [Nontrivial S] {y y' y'' : FrPt Xo c S}
    (h' : levR (gM, LinearMap.id) y y') (h'' : levR (gM, LinearMap.id) y y'') : y' = y'' := by
  obtain ⟨ρ, ν, i, h, hm⟩ := h'
  obtain ⟨ρ', ν', i', g, gm⟩ := h''
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let φ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  have hinj := reflects_half_of_move h (AlgebraicClosure (S ⧸ m)) (spMap φ ≫ y.x)
    (φ.comp ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)) (by
      rw [Category.assoc, y.x_over]
      unfold sOf spMap
      rw [← Spec.map_comp]; rfl)
  obtain ⟨rfl, e⟩ := GlobalTheory.T.levelMove_moduli_unique_universalTriple E H Dw l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h g
    (GlobalTheory.exists_sim_of_aut_mod E H Dw l l.A gM hpq l.A_pos hA hinj)
  exact (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν' e.symm hm gm

end Move

section Idem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GoodLatCompare

def ofList {G L : Type} [Group G] [Finite G] [Field L] (eC : G → L) : MonoidAlgebra L G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm eC)

end Idem

section Framed

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Framed

section Swap

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def sw (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Af F ⊗[F] E ≃+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv

def clos (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (Fin n → E)) :
    AddSubgroup (Fin n → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ Λ, z = fun i => a ⊗ₜ x i}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Swap

section Half

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Lev Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

end Half

end GlobalTheory.LevelSpanCompare
