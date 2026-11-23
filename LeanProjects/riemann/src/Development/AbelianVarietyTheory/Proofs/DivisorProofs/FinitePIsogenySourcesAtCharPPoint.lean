import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.SourceFin

open GlobalTheory.UPel.HT.ESDual GlobalTheory.UPel.HT.ES.CorrQF

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}
    (m : ObjMap o' o f) (e : ℕ) : ObjMap (scale o' e rfl) (scale o e rfl) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem exists_scale_mono (hN : 0 < N) (hp : N.Coprime p) (M : Model b N) (e : ℕ) :
    ∃ τ : M.X ⟶ M.X, Mono τ ∧ τ ≫ M.s = M.s ∧ Nonempty (ObjMap (scale M.univ e rfl) M.univ τ) := by
  obtain ⟨f, hf⟩ := exists_inv_exp hN hp e
  obtain ⟨τ, ⟨hτ, ⟨m⟩⟩, -⟩ := M.rep _ _ (scale M.univ e rfl)
  obtain ⟨τ', ⟨hτ', ⟨m'⟩⟩, -⟩ := M.rep _ _ (scale M.univ f rfl)
  have n : ObjMap (scale (scale M.univ e rfl) f rfl) M.univ (𝟙 M.X) :=
    { φ := (idMap M.univ).φ
      φ₂ := (idMap M.univ).φ₂
      cart := (idMap M.univ).cart
      sq := (idMap M.univ).sq
      act := (idMap M.univ).act
      pol := (idMap M.univ).pol
      eta := fun y => by
        have h : (scale (scale M.univ e rfl) f rfl).eta y = M.univ.eta y := by
          show M.univ.eta (p ^ e • p ^ f • y) = _
          rw [smul_smul, ← pow_add, eta_congr M.univ hf (pow_pos (Fact.out : p.Prime).pos _)]
        rw [h]
        exact (idMap M.univ).eta y }
  have h1 : τ ≫ τ' = 𝟙 M.X :=
    (M.rep _ _ (scale (scale M.univ e rfl) f rfl)).unique
      ⟨by rw [Category.assoc, hτ', hτ], ⟨compMap (scaleMap m f) m'⟩⟩ ⟨Category.id_comp _, ⟨n⟩⟩
  exact ⟨τ, mono_of_mono_fac h1, hτ, ⟨m⟩⟩

theorem exists_isPIsog_scale {S : Scheme.{0}} {s : S ⟶ Sp R} {e : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog (p ^ e) o o' ψ) : ∃ ψ' : o'.A ⟶ (scale o e rfl).A, IsPIsog (p ^ e) o' (scale o e rfl) ψ' := by
  obtain ⟨ψ', hm, h₁, h₂⟩ := hψ.2.2.2.2.2
  obtain ⟨a, l, P⟩ := dual_clauses hψ h₁ h₂
  exact ⟨ψ', ⟨e, rfl⟩, hm, a, l, P, ψ, hψ.2.1, h₂, h₁⟩

theorem not_mem_basicOpen {X : Scheme.{0}} (z : X) {k : Type} [Field k] [CharP k p]
    (h : X.residueField z →+* k) : z ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  rw [Scheme.mem_basicOpen_top, map_natCast]
  intro hu
  have := hu.map (h.comp (X.residue z).hom)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

theorem exists_residueField_hom {X : Scheme.{0}} {k : Type} [Field k] (ζ : Sp k ⟶ X) {z : X}
    (hz : ζ (IsLocalRing.closedPoint k) = z) :
    ∃ h : X.residueField z →+* k, spMap h ≫ X.fromSpecResidueField z = ζ := by
  subst hz
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ζ)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X ζ⟩

theorem finite_isogSource : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp _ c hm M z
  set Z := {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} with hZ
  rcases Z.eq_empty_or_nonempty with h0 | ⟨u₀, k₀, _, _, _, ζ₀, _, _, _, -, -, _, -, hψ₀, hz₀, -⟩
  · rw [h0]; exact Set.finite_empty
  obtain ⟨e, rfl⟩ := hψ₀.1
  obtain ⟨h₀, -⟩ := exists_residueField_hom ζ₀ hz₀
  have hz := not_mem_basicOpen (p := p) z h₀
  obtain ⟨τ, hmono, hτ, ⟨mτ⟩⟩ := exists_scale_mono (by omega) hNp M e
  have key : ∀ u : Z, ∃ (k : Type) (_ : Field k) (σ : M.X.residueField z →+* k) (υ : Sp k ⟶ M.X),
      (∀ q, υ q = u.1) ∧ IsogTarget M (p ^ e) (spMap σ ≫ M.X.fromSpecResidueField z) (υ ≫ τ) := by
    rintro ⟨u, k, _, _, _, ζ, υ, ou, oz, mu, mz, ψ, hs, hψ, hζ, hu⟩
    obtain ⟨σ, hσ⟩ := exists_residueField_hom ζ hζ
    obtain ⟨ψ', hψ'⟩ := exists_isPIsog_scale hψ
    refine ⟨k, inferInstance, σ, υ, fun q => ?_, ?_⟩
    · rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
      exact hu
    · rw [hσ]
      exact ⟨by rw [Category.assoc, hτ, hs], oz, scale ou e rfl, ψ', ⟨mz⟩, ⟨compMap (scaleMap mu e) mτ⟩, hψ'⟩
  choose k hk σ υ hυ hT using key
  obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField z) Z k σ
  have hfin := (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm (p ^ e) M z hz L h).preimage
    (f := fun υ' : Sp L ⟶ M.X => υ' ≫ τ) (fun x _ y _ hxy => (cancel_mono τ).1 hxy)
  refine (Set.Finite.biUnion hfin fun υ' _ => Set.finite_range (fun q : Sp L => υ' q)).subset ?_
  intro u hu
  have h1 := isogTarget_spMap p D R b N M (p ^ e) (k ⟨u, hu⟩) L (g ⟨u, hu⟩) _ _ (hT ⟨u, hu⟩)
  have e1 : spMap (g ⟨u, hu⟩) ≫ spMap (σ ⟨u, hu⟩) ≫ M.X.fromSpecResidueField z =
      spMap h ≫ M.X.fromSpecResidueField z := by
    rw [← Category.assoc, ← hg ⟨u, hu⟩]
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [e1, ← Category.assoc] at h1
  simp only [Set.mem_iUnion, Set.mem_range]
  refine ⟨spMap (g ⟨u, hu⟩) ≫ υ ⟨u, hu⟩, h1, Classical.arbitrary _, ?_⟩
  rw [Scheme.Hom.comp_apply, hυ ⟨u, hu⟩ _]

end GlobalTheory.UPel.HT.ES.SourceFin
