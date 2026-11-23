import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ChQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FgChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_surj {B E E' P : Type} [CommRing B] [Ring E] [Ring E'] [Ring P] [Algebra B E] [Algebra B E']
    [Algebra B P] (q : E →ₐ[B] E') (hq : Function.Surjective q) (ρ : E →ₐ[B] P) (h : ∀ x, q x = 0 → ρ x = 0) :
    ∃ π : E' →ₐ[B] P, ∀ x, π (q x) = ρ x := by
  have key : ∀ x y, q x = q y → ρ x = ρ y := fun x y hxy =>
    sub_eq_zero.1 (by rw [← map_sub]; exact h _ (by rw [map_sub, hxy, sub_self]))
  choose s hs using hq
  have hq' : ∀ x, ρ (s (q x)) = ρ x := fun x => key _ _ (hs _)
  refine ⟨⟨⟨⟨⟨fun y => ρ (s y), ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun r => ?_⟩, hq'⟩
  · rw [← map_one q, hq', map_one]
  · change ρ (s (a * b)) = ρ (s a) * ρ (s b)
    rw [← map_mul]
    exact key _ _ (by rw [map_mul, hs, hs, hs])
  · change ρ (s 0) = 0
    rw [← map_zero q, hq', map_zero]
  · change ρ (s (a + b)) = ρ (s a) + ρ (s b)
    rw [← map_add]
    exact key _ _ (by rw [map_add, hs, hs, hs])
  · change ρ (s (algebraMap B E' r)) = _
    rw [← q.commutes, hq', ρ.commutes]

theorem UpperTheory.V.Th.Coc.gma :
    ∀ {n : ℕ} {O R G : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → ∃ (E : Type) (_ : Ring E) (_ : Algebra R E) (π : MonoidAlgebra R G →ₐ[R] E) (τ : E →ₗ[R] R) (e : Fin n → E), Function.Surjective π ∧ (∀ y, τ (π y) = D.tr y) ∧ IsTrGMA τ e := by
  intro n O R G _ _ _ _ _ _ D χ hn hχ hred
  obtain ⟨E, _, _, q, DE, hsurj, hDE, hCH, -⟩ := chQuot D.toDet
  obtain ⟨π0, hs0, -, -, hchi0⟩ := CA.f_chars χ hχ
  letI : Algebra R (ResidueField O) := (res O R : R →+* ResidueField O).toAlgebra
  have hal : algebraMap R (ResidueField O) = (res O R : R →+* ResidueField O) := rfl
  let ρ : MonoidAlgebra R G →ₐ[R] (Fin n → ResidueField O) :=
    (π0.restrictScalars R).comp (MonoidAlgebra.mapAlgHom G (Algebra.ofId R (ResidueField O)))
  have hρ : ∀ x, ρ x = π0 (MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x) := fun x => rfl
  have hchi : ∀ x, (DE.chi (q x)).map (res O R : R →+* ResidueField O) = ∏ i, (Polynomial.X - Polynomial.C (ρ x i)) := fun x => by
    rw [← (CA.d_pull DE q).1, hDE, (CA.d_toDet D x).1, ← ((CA.d_gmap D).2.2.1 (res O R : R →+* ResidueField O) x).1, hred, hρ]
    exact hchi0 _
  have hker : ∀ x, q x = 0 → ρ x = 0 := fun x hx => by
    have h1 := hchi x
    rw [hx, ← map_zero q, hchi 0, map_zero] at h1
    funext i
    have h2 := congrArg (Polynomial.eval (ρ x i)) h1
    rw [Polynomial.eval_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero (f := fun j => Polynomial.eval (ρ x i) (Polynomial.X - Polynomial.C (ρ x j)))
      (Finset.mem_univ i) (by simp)] at h2
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2
    simpa using hj
  obtain ⟨π, hπ⟩ := lift_surj q hsurj ρ hker
  have hmap : ∀ y : MonoidAlgebra (ResidueField O) G, ∃ x, MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x = y := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | single g r =>
      obtain ⟨c, rfl⟩ := residue_surjective r
      exact ⟨MonoidAlgebra.single g (algebraMap O R c), (MonoidAlgebra.mapRingHom_single _ _ _).trans
        (congrArg _ ((res O R).commutes c))⟩
  have hπs : Function.Surjective π := fun v => by
    obtain ⟨y, rfl⟩ := hs0 v
    obtain ⟨x, rfl⟩ := hmap y
    exact ⟨q x, by rw [hπ, hρ]⟩
  have hchiE : ∀ x, (DE.chi x).map (algebraMap R (ResidueField O)) = ∏ i, (Polynomial.X - Polynomial.C (π x i)) := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hπ, hal, hchi]
  haveI : IsLocalHom (algebraMap R (ResidueField O)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero ((res_eq_zero_iff O R a).2 hn)⟩
  obtain ⟨-, e, he, -⟩ := CA.f_gma DE π hCH hπs hchiE
  obtain ⟨h1, h2, -⟩ := CA.d_tr DE
  obtain ⟨t, ht⟩ := h1 hn
  have hc := fun i => CA.d_corner DE (e i) he.ch (he.idem.idem i) (he.rank i) hn
  refine ⟨E, _, _, q, t, e, hsurj, fun y => ?_, fun a b => ?_, he.idem, fun i a => ?_, fun i => ?_⟩
  · rw [ht, ← (CA.d_toDet D y).2.2.1, ← hDE]
    unfold Det.tr Det.lam
    rw [(CA.d_pull DE q).1]
  · rw [ht, ht]
    exact h2 1 a b
  · rw [ht]
    exact (hc i).1 a
  · rw [ht]
    exact (hc i).2.1
