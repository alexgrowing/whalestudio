import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsExponentialUniformization
import Development.AutomorphicArithmetic.DivisorFrames.ExponentialHermitianHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Cartier
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.GradedNorm GlobalTheory.Mean4O
open scoped ComplexOrder

private theorem below_map {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {X : Scheme.{0}} (q : Sp K ⟶ X) :
    below (spMap ι ≫ q) = below q := by
  show q ((spMap ι) (IsLocalRing.closedPoint K')) = q _
  rw [Subsingleton.elim ((spMap ι) (IsLocalRing.closedPoint K')) (IsLocalRing.closedPoint K)]

private theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR (g.comp f)) = spMap (dualMap g) ≫ spMap (Chart.dualMapR f) := by
  rw [← sp_comp]
  congr 1
  ext r <;> simp [dualMap, Chart.dualMapR]

theorem UpperTheory.hermitian_distinct_letters_orthogonal :
    ∀ (D : D7) (O : Setup D) (y : Pad.Pt O.s), below y.y ∉ genBd O.s.T.Z → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → ∀ (θ : Qb →+* ℂ), Formalism.L2.PjFree.GoodEmb O.κ.c (θ.comp y.fK) → ∀ (k k' : Fin F.P₀.g) (a a' : Pad.Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some a → (letters O.S.Dw)[(k' : ℕ)]? = some a' → a.1 ≠ a'.1 → h.form (θ.comp ι) (Pi.single k 1) (Pi.single k' 1) = 0 := by
  intro D O y hy K _ _ F ι h hT hH θ hG k k' a a' ha ha' hne
  classical
  obtain ⟨jF, yO, ψ, -, h2, h3, h4, h5, h6⟩ := hT
  obtain ⟨Λ, Hm, W, ⟨Q, e, ψ', v', u, χ, ⟨-, p1, p2⟩, -, hAH, hv⟩, hW⟩ := hH (θ.comp ι)
  let yc : GlobalTheory.CxPts (genStr O.s.T.Z) (θ.comp y.fK) :=
    ⟨spMap θ ≫ y.y, by rw [Category.assoc, y.y_over, sp_comp]⟩
  have hyc : yc.1 = spMap θ ≫ y.y := rfl
  obtain ⟨f, hf⟩ := y.frame.exists_isMap (φ' := θ.comp y.fK) (x' := yc.1 ≫ genι O.s.T.Z) θ rfl
    (by rw [hyc, Category.assoc])
  have hΨ : IsGrpPullback Q.A O.s.T.Z.t.G (yc.1 ≫ genι O.s.T.Z) (ψ' ≫ F.φ ≫ ψ) := by
    refine (IsGrpPullback.comp p1 (IsGrpPullback.comp F.fib h3)).congr ?_ rfl
    rw [hyc, Category.assoc, ← h2, sp_comp, sp_comp, Category.assoc, Category.assoc]
  have hL : LBIso (O.s.T.Z.t.PP.L.pull (ψ' ≫ F.φ ≫ ψ)) Q.L := by
    refine LBIso.trans (pull_isLB O.s.T.Z.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ') Q.isLB ?_ p2
    exact h4.chartPull (Geo.Tor.chartPullSame _ _ (fun _ => F.φ ≫ ψ) _ ψ' fun _ => rfl)
      (Geo.Tor.chartPullPull _ ψ' ψ' rfl)
  obtain ⟨exx, hex, hhol, hint, hd⟩ := UpperTheory.exists_exponential_uniformization _ _ _ O.s.T.Z.t _ Q _ hΨ hL _ u Hm χ hAH
  have hb : yc.1 (IsLocalRing.closedPoint ℂ) ∉ genBd O.s.T.Z := by
    show below yc.1 ∉ _
    rw [hyc, below_map]
    exact hy
  have hex' : ∀ (t : D.host.E →+* ℂ) (c : Fin (O.S.Dw.mult t)), ∃ q : Fin F.P₀.g,
      (letters O.S.Dw)[(q : ℕ)]? = some ⟨t, c⟩ := fun t c => by
    obtain ⟨n, hn⟩ := (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective O.S.Dw).2 ⟨t, c⟩
    exact ⟨⟨n, n.2.trans_eq h5.symm⟩, List.getElem?_eq_some_iff.2 ⟨n.2, hn⟩⟩
  choose q hq using hex'
  have hqk : ∀ (j : Fin F.P₀.g) (b : Pad.Letter O.S.Dw), (letters O.S.Dw)[(j : ℕ)]? = some b →
      q b.1 b.2 = j := fun j b hb => by
    obtain ⟨n1, e1⟩ := List.getElem?_eq_some_iff.1 hb
    obtain ⟨n2, e2⟩ := List.getElem?_eq_some_iff.1 (hq b.1 b.2)
    have := (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective O.S.Dw).1 (a₁ := ⟨_, n2⟩) (a₂ := ⟨_, n1⟩) (e2.trans e1.symm)
    exact Fin.ext (Fin.mk.inj_iff.1 this)
  have ev : ∀ t c, f.v t c = (v' (q t c)).left ≫ ψ' ≫ F.φ ≫ ψ := fun t c => by
    have e1 : (v' (q t c)).left ≫ ψ' = _ := (hv (q t c)).1
    have e2 := h6 (q t c) _ (hq t c)
    rw [hf t c, ← Category.assoc, e1, dual_comp, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e2
  have key := UpperTheory.exponential_hermitian_holomorphic D O _ hG yc hb _ exx Hm hex hhol hint f (fun t c => W (q t c)) (fun t c => by
    rw [ev]
    refine hd _ _ ((UpperTheory.isTangent_iff_pullback O.s.T.Z.t hΨ _).2 ?_) (hv _).2
    rw [← ev]
    exact f.tan t c) a'.1 a.1 a'.2 a.2 hne.symm
  simp only [hqk k a ha, hqk k' a' ha'] at key
  rw [hW, key, mul_zero]
