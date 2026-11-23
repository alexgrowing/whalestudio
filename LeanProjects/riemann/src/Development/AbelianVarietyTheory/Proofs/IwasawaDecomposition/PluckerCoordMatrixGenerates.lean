import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordChangeStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerRegularImpliesGenerationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerMatricesLowerTriangularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeCoordTransitionStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkLoc

theorem eq_of_toProj_plkSec_eq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → (∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1)) (y : (Φ.C k).Y.X), y ∈ (Φ.C k).π ⁻¹ᵁ V → (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).RegularAt y (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q)) → ∀ (ht : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ⨆ q, nonzeroLocus (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x q) = ⊤) (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = a' ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) → (∀ x, a ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x) = a' ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x)) → a = a' := by
  intro D A N j S κ s Φ k V hV φ g hst hg hne B hB hreg ht K _ _ a a' hf hP
  obtain ⟨c, hc⟩ : ∃ c : Γ(gen s.T.Z, V) →+* K, a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c :=
    ⟨(Spec.preimage (a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom))).hom, by simp [spMap]⟩
  have hc' : a' ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c := hf ▸ hc
  obtain ⟨y, ψ, P, T, hp, ⟨h, hcar, hco⟩, hPu, hBT, hT, hd⟩ := GlobalTheory.T.plucker_coord_change_stable D A N j S κ s Φ k V hV φ g hst hg hne B hB K a c hc
  obtain ⟨y', ψ', P', T', hp', ⟨h', hcar', hco'⟩, hPu', hBT', hT', hd'⟩ :=
    GlobalTheory.T.plucker_coord_change_stable D A N j S κ s Φ k V hV φ g hst hg hne B hB K a' c hc'
  have hv := GlobalTheory.T.plucker_regular_implies_generation D A N j S κ s Φ k V hV B hreg ht K a c hc y ψ P T hp hPu hBT hT hd
  have hv' := GlobalTheory.T.plucker_regular_implies_generation D A N j S κ s Φ k V hV B hreg ht K a' c hc' y' ψ' P' T' hp' hPu' hBT' hT' hd'
  have hu : ∀ x, ∃ u : Kˣ, GlobalTheory.FlagAmple.PlkLoc.plkFn (P.map ψ) x =
      (u : K) • GlobalTheory.FlagAmple.PlkLoc.plkFn (P'.map ψ') x := by
    intro x
    obtain ⟨e1, he1⟩ := hv x
    obtain ⟨e2, he2⟩ := hv' x
    have e := hP x
    rw [he1, he2] at e
    obtain ⟨u, hu⟩ := (GlobalTheory.ProjSpace.pt_eq_pt_iff c e2 e1).1 e.symm
    exact ⟨u, hu⟩
  have hdet : ∀ τ, IsUnit ((P.map ψ) τ).det := fun τ => by
    have := (hPu τ).map ψ; rw [RingHom.map_det] at this; exact this
  have hdet' : ∀ τ, IsUnit ((P'.map ψ') τ).det := fun τ => by
    have := (hPu' τ).map ψ'; rw [RingHom.map_det] at this; exact this
  obtain ⟨d, hdT⟩ := GlobalTheory.T.eigenframe_coord_transition D A N j S κ s V hV φ g K c h h' (P.map ψ) (P'.map ψ') hco hco' hdet hdet'
    (GlobalTheory.T.plucker_matrices_lower_triangular D A N j S K _ _ hdet hdet' hu)
  have hcar2 : (Φ.C k).Carries (a' ≫ ((Φ.C k).π ⁻¹ᵁ V).ι) h := by
    obtain ⟨y1, ψ1, φ1, f1, t1, t1', e1, e2, e3⟩ := hcar'
    exact ⟨y1, ψ1, φ1, f1, t1, _, e1, e2, GlobalTheory.ShFam.FlatSec.tri_trans e3 hdT⟩
  have hx : (spMap c ≫ hV.fromSpec) ≫ genStr s.T.Z = spMap (c.comp φ) := by
    rw [Category.assoc, hst]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hpt : ∀ b : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme, b ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c →
      (b ≫ ((Φ.C k).π ⁻¹ᵁ V).ι) ≫ (Φ.C k).π = spMap c ≫ hV.fromSpec := by
    intro b hb
    rw [← hV.isoSpec_inv_ι, ← hb, Category.assoc, ← morphismRestrict_ι]
    simp
  obtain ⟨p0, -, huniq⟩ := Φ.lifts K (c.comp φ) (spMap c ≫ hV.fromSpec) hx h
  have e1 := huniq ⟨k, a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι⟩ ⟨hpt a hc, hcar⟩
  have e2 := huniq ⟨k, a' ≫ ((Φ.C k).π ⁻¹ᵁ V).ι⟩ ⟨hpt a' hc', hcar2⟩
  have e4 : a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι = a' ≫ ((Φ.C k).π ⁻¹ᵁ V).ι :=
    eq_of_heq (Sigma.mk.inj_iff.1 (e1.trans e2.symm)).2
  exact (cancel_mono _).1 e4

end GlobalTheory.FlagAmple.PlkLoc
