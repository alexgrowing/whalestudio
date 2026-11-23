import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFramesStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Valu

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_surj {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem exists_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.affineOpens) (hx : x (IsLocalRing.closedPoint A) ∈ (U.1 : Set X)) :
    ∃ φ : Γ(X, U.1) →+* A, x = spMap φ ≫ U.2.fromSpec := by
  have htop : x ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem x hx
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y ∈ x ⁻¹ᵁ U.1 := by rw [htop]; trivial
    exact this
  have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  obtain ⟨φ, hφ⟩ := sp_surj (B := Γ(X, U.1)) (@IsOpenImmersion.lift _ _ _ U.2.fromSpec x hi hr)
  exact ⟨φ, (@IsOpenImmersion.lift_fac _ _ _ U.2.fromSpec x hi hr).symm.trans (congrArg (· ≫ U.2.fromSpec) hφ)⟩

theorem indep_cellVec {T : Type} {m : T → ℕ} {k : Type} [Field k] {M : ℕ} (D c : Let m → Fin (M + 1) → k) (w : Pm m)
    (x : CellVar m → k) (h : LeftInv D c) (τ : T) :
    LinearIndependent k fun j : Fin (m τ) => cellVec c w x ⟨τ, j⟩ := by
  have h1 := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m k M D c w x h).1 _ _ (down_std τ (m τ) le_rfl)
  rw [GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.1] at h1
  have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (h1.trans_ne one_ne_zero)
  let L : (Fin (M + 1) → k) →ₗ[k] (Fin (m τ) → k) :=
    Matrix.toLin' (Matrix.of fun l' r => D ((wLet w ∘ std τ (m τ) le_rfl) l') r)
  exact LinearIndependent.of_comp L h2

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S ι : Type} [CommRing S] {c c' : Let m → ι → S} (h : InBlock c c')
    (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_uvec {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (ψ : CR m U →+* S) :
    (fun z => ψ ∘ uvec c w z) =
      cellVec (fun z => (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ∘ c z) w (ψ ∘ MvPolynomial.X) :=
  funext fun z => map_cellVec ψ _ w _ z

theorem sp_cbase {X : Scheme.{0}} {T : Type} {m : T → ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (ψ : CR m U →+* S) :
    spMap ψ ≫ cbase m U = spMap (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ≫ U.2.fromSpec := by
  rw [cbase, ← Category.assoc, sp_comp]

theorem exists_integral_cell : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP A k _ _ _ _ _ _ b' w' a x hx ha
  obtain ⟨ψ', rfl⟩ := sp_surj a
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hx ⟨IsLocalRing.closedPoint A, rfl⟩)
  obtain ⟨φ, rfl⟩ := exists_of_closedPoint x (V b) hb
  have ha' : spMap ((algebraMap A k).comp φ) ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← sp_cbase, ha, ← Category.assoc, sp_comp]
  obtain ⟨w, y, d, hy, hd, ht⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField T m k (ValuationRing.valuation A k).valuationSubring M _ _
    (inBlock_cellVec (hC.compat k b b' _ _ ha') w' (ψ' ∘ MvPolynomial.X))
    (indep_cellVec _ _ w' _ ((hC.inv b').map _))
  have hy' : ∀ v, ∃ t : A, algebraMap A k t = y v := fun v => (ValuationRing.mem_integer_iff A k (y v)).1 (hy v)
  choose t hyt using hy'
  let χ : CR m (V b) →+* A := MvPolynomial.eval₂Hom φ t
  have hχ : χ.comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) = φ := MvPolynomial.eval₂Hom_comp_C φ t
  have hχ' : ((algebraMap A k).comp χ).comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) =
      (algebraMap A k).comp φ := by rw [RingHom.comp_assoc, hχ]
  refine ⟨b, w, spMap χ, by rw [sp_cbase, hχ], ?_⟩
  rw [← Category.assoc, sp_comp]
  refine GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hC hP k b b' w w' _ ψ' d ?_ hd ?_
  · rw [sp_cbase, sp_cbase, hχ', ha']
  · have e : ((algebraMap A k).comp χ) ∘ MvPolynomial.X = y := funext fun v => by
      rw [← hyt]
      exact congrArg (algebraMap A k) (MvPolynomial.eval₂Hom_X' φ t v)
    rw [map_uvec, map_uvec, hχ', e]
    exact ht

end GlobalTheory.FlagEmb.Valu
