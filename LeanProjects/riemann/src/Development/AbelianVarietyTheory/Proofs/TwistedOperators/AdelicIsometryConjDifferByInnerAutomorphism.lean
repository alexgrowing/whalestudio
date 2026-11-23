import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InnerTwist

theorem exists_inv {R : Type} [CommRing R] {m n : ℕ} (j : Matrix (Fin m) (Fin n) R)
    (h : Function.Bijective j.mulVec) : ∃ j' : Matrix (Fin n) (Fin m) R, j * j' = 1 ∧ j' * j = 1 := by
  let e := LinearEquiv.ofBijective (Matrix.mulVecLin j) h
  refine ⟨LinearMap.toMatrix' (e.symm : (Fin m → R) →ₗ[R] (Fin n → R)), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    exact e.apply_symm_apply x
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    exact e.symm_apply_apply x

variable {D : D7}

theorem mat_ext {k l : Type} (X Y : Matrix k l (AF D.host.F ⊗[D.host.F] D.host.E))
    (h1 : X.map (GlobalTheory.FinIsoGrp.pInf D) = Y.map (GlobalTheory.FinIsoGrp.pInf D))
    (h2 : X.map (GlobalTheory.FinIsoGrp.qFin D) = Y.map (GlobalTheory.FinIsoGrp.qFin D)) : X = Y := by
  ext i i'
  exact GlobalTheory.FinIsoGrp.proj_inj D _ _ (congrFun (congrFun h1 i) i') (congrFun (congrFun h2 i) i')

theorem infHom_val (V : HSp D) (g : GA D V) :
    (infHom V g).val = (matHom V g).val.map (GlobalTheory.FinIsoGrp.pInf D) := by
  refine Matrix.ext fun i k => ?_
  rfl

theorem gfc_ext (V : HSp D) (x y : GfC V)
    (h : (finE V (x : GA D V)).val = (finE V (y : GA D V)).val) : x = y := by
  have hx : infHom V (x : GA D V) = 1 := x.2
  have hy : infHom V (y : GA D V) = 1 := y.2
  have hm : (matHom V (x : GA D V)).val = (matHom V (y : GA D V)).val := by
    apply mat_ext
    · rw [← infHom_val, ← infHom_val, hx, hy]
    · rw [← GlobalTheory.FinIsoGrp.finE_val, ← GlobalTheory.FinIsoGrp.finE_val, h]
  have inj : Function.Injective (matHom V) := Subgroup.subtype_injective _
  exact Subtype.ext (inj (Units.ext hm))

end GlobalTheory.InnerTwist

namespace GlobalTheory.InnerTwist

variable {D : D7}

theorem map_one' {R S : Type} [CommRing R] [CommRing S] {n : Type} [Fintype n] [DecidableEq n] (f : R →+* S) :
    (1 : Matrix n n R).map f = 1 :=
  Matrix.map_one _ (RingHom.map_zero f) (RingHom.map_one f)

theorem lift_abs {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (σ₁ : R₁ →+* R₁) (σ₂ : R₂ →+* R₂) (p : R →+* R₁) (q : R →+* R₂)
    (hinj : ∀ x y, p x = p y → q x = q y → x = y) (s : R₂ → R) (hs1 : ∀ y, p (s y) = 0) (hs2 : ∀ y, q (s y) = y)
    (hp : ∀ x, p (σ x) = σ₁ (p x)) (hq : ∀ x, q (σ x) = σ₂ (q x)) (J : Matrix n n R) (X Y : Matrix n n R₂)
    (hXY : X * Y = 1) (hYX : Y * X = 1) (hX : Formalism.UG.cT σ₂ X * J.map q * X = J.map q) :
    ∃ u : GL n R, Formalism.UG.cT σ (u : Matrix n n R) * J * (u : Matrix n n R) = J ∧
      (u : Matrix n n R).map p = 1 ∧ (u : Matrix n n R).map q = X := by
  have ext : ∀ {k l : Type} (A B : Matrix k l R), A.map p = B.map p → A.map q = B.map q → A = B := by
    intro k l A B ha hb
    ext i i'
    exact hinj _ _ (congrFun (congrFun ha i) i') (congrFun (congrFun hb i) i')
  let lift : Matrix n n R₂ → Matrix n n R := fun Z => (1 - s 1) • (1 : Matrix n n R) + Z.map s
  have lp : ∀ Z, (lift Z).map p = 1 := by
    intro Z; ext i k
    by_cases h : i = k <;> simp [lift, Matrix.one_apply, h, hs1]
  have lq : ∀ Z, (lift Z).map q = Z := by
    intro Z; ext i k
    by_cases h : i = k <;> simp [lift, Matrix.one_apply, h, hs2]
  have hmul : ∀ Z W : Matrix n n R₂, Z * W = 1 → lift Z * lift W = 1 := by
    intro Z W hZW
    apply ext
    · rw [Matrix.map_mul, lp, lp, Matrix.one_mul, map_one']
    · rw [Matrix.map_mul, lq, lq, hZW, map_one']
  have cp : ∀ A : Matrix n n R, (Formalism.UG.cT σ A).map p = Formalism.UG.cT σ₁ (A.map p) := by
    intro A; ext i k; exact hp _
  have cq : ∀ A : Matrix n n R, (Formalism.UG.cT σ A).map q = Formalism.UG.cT σ₂ (A.map q) := by
    intro A; ext i k; exact hq _
  refine ⟨⟨lift X, lift Y, hmul X Y hXY, hmul Y X hYX⟩, ?_, lp X, lq X⟩
  show Formalism.UG.cT σ (lift X) * J * lift X = J
  apply ext
  · rw [Matrix.map_mul, Matrix.map_mul, cp, lp, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, cq, lq]
    exact hX

theorem exists_fin (V : HSp D) (X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) X *
        V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * X =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) :
    ∃ b : GfC V, (finE V (b : GA D V)).val = X := by
  choose s hs1 hs2 using GlobalTheory.FinIsoGrp.proj_surj D
  rw [← GlobalTheory.FinIsoGrp.gram_map] at hX
  obtain ⟨u, hu, hup, huq⟩ := lift_abs (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf D.host.F) D.sp.cm.sig) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (GlobalTheory.FinIsoGrp.pInf D) (GlobalTheory.FinIsoGrp.qFin D) (GlobalTheory.FinIsoGrp.proj_inj D) s hs1 hs2
    (fun x => GlobalTheory.FinIsoGrp.map_sig (fstA D.host.F) D.sp.cm.sig x) (GlobalTheory.FinIsoGrp.qFin_sig D)
    (JR (AF D.host.F) V.gram) X Y hXY hYX hX
  let b0 : GA D V := (⟨u, hu⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hb : infHom V b0 = 1 := by
    apply Units.ext
    exact (infHom_val V b0).trans hup
  refine ⟨⟨b0, hb⟩, ?_⟩
  rw [GlobalTheory.FinIsoGrp.finE_val]
  exact huq

theorem alg {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (σ : R →+* R) (j j₀ : Matrix m n R) (j' k' : Matrix n m R) (G : Matrix n n R) (G' : Matrix m m R)
    (h1 : j * j' = 1) (h2 : j' * j = 1) (k1 : j₀ * k' = 1) (k2 : k' * j₀ = 1)
    (hJ : Formalism.UG.cT σ j * G' * j = G) (hJ₀ : Formalism.UG.cT σ j₀ * G' * j₀ = G) :
    Formalism.UG.cT σ (k' * j) * G * (k' * j) = G ∧ (k' * j) * (j' * j₀) = 1 ∧ (j' * j₀) * (k' * j) = 1 := by
  have hk : Formalism.UG.cT σ k' * G * k' = G' := by
    calc Formalism.UG.cT σ k' * G * k' = Formalism.UG.cT σ (j₀ * k') * G' * (j₀ * k') := by
          rw [← hJ₀, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G' := by rw [k1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k' * j) * G * (k' * j) = Formalism.UG.cT σ j * (Formalism.UG.cT σ k' * G * k') * j := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hk, hJ]
  · calc (k' * j) * (j' * j₀) = k' * (j * j') * j₀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, k2]
  · calc (j' * j₀) * (k' * j) = j' * (j₀ * k') * j := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [k1, Matrix.mul_one, h2]

theorem alg2 {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (j j₀ : Matrix m n R) (j' k' : Matrix n m R) (h1 : j * j' = 1) (k1 : j₀ * k' = 1)
    (P Q : Matrix m m R) (A : Matrix n n R) (c1 : P * j = j * A) (c2 : Q * j₀ = j₀ * ((k' * j) * A * (j' * j₀))) :
    P = Q := by
  have e1 : P = j * A * j' := by
    calc P = P * (j * j') := by rw [h1, Matrix.mul_one]
      _ = j * A * j' := by rw [← Matrix.mul_assoc, c1]
  have e2 : Q = j * A * j' := by
    calc Q = Q * (j₀ * k') := by rw [k1, Matrix.mul_one]
      _ = (j₀ * k') * j * A * j' * (j₀ * k') := by
          rw [← Matrix.mul_assoc, c2]; simp only [Matrix.mul_assoc]
      _ = j * A * j' := by rw [k1, Matrix.one_mul, Matrix.mul_one]
  rw [e1, e2]

theorem inv_val {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (u : GL n R) (X Y : Matrix n n R)
    (hu : u.val = X) (hYX : Y * X = 1) : (u⁻¹).val = Y := by
  calc (u⁻¹).val = (Y * X) * (u⁻¹).val := by rw [hYX, Matrix.one_mul]
    _ = Y * (u.val * (u⁻¹).val) := by rw [hu]; simp only [Matrix.mul_assoc]
    _ = Y := by rw [Units.mul_inv, Matrix.mul_one]

theorem conj_inner : ∀ (D : D7) (V V' : HSp D) (j j₀ : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j₀ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j₀ Φ₀ → ∃ b : GfC V, ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D V V' j j₀ Φ Φ₀ hj hj₀ hΦ hΦ₀
  obtain ⟨j', h1, h2⟩ := exists_inv j hj.1
  obtain ⟨k', k1, k2⟩ := exists_inv j₀ hj₀.1
  obtain ⟨hX, hXY, hYX⟩ := alg _ j j₀ j' k' _ _ h1 h2 k1 k2 hj.2 hj₀.2
  obtain ⟨b, hb⟩ := exists_fin V _ _ hXY hYX hX
  refine ⟨b, fun g => gfc_ext V' _ _ ?_⟩
  have hbinv := inv_val (finE V (b : GA D V)) _ _ hb hYX
  have e0 : (finE V ((b * g * b⁻¹ : GfC V) : GA D V)).val =
      HMul.hMul (HMul.hMul (HMul.hMul k' j) (finE V (g : GA D V)).val) (HMul.hMul j' j₀) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      hbinv, hb]
  have c2 := hΦ₀ (b * g * b⁻¹)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul at c2
  rw [e0] at c2
  exact alg2 j j₀ j' k' h1 k1 _ _ _ (hΦ g) c2

end GlobalTheory.InnerTwist
