import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section SlopeTestRemainingChoices

open GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
  {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem pull_primPull (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (e : A ⟶ A) (e' : A' ⟶ A')
    [IsMonHom e] [IsMonHom e'] (he : e'.left ≫ φ = φ ≫ e.left) (c : primDR A) :
    (bcMor h).pull (primPull (dp0 R) (𝟙 _) e c) = primPull (dp0 R') (𝟙 _) e' ((bcMor h).pull c) := by
  have e1 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) e) (bcMor h)
    (GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) rfl c
  have e2 := GrpMor.pull_pull (bcMor h) (homMor (dp0 R') (𝟙 _) e')
    (GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) he c
  exact e1.trans e2.symm

private theorem pull_frob_iter (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (f : ℕ) (c : primDR A) :
    (bcMor h).pull ((frobDR p R hR A)^[f] c) = (frobDR p R' hR' A')^[f] ((bcMor h).pull c) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', GlobalTheory.LinFrob.pull_frobDR p hR hR' h, ih]

private theorem frob_iter_smul (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (f : ℕ) (r : R) (c : primDR A) :
    (frobDR p R hR A)^[f] (r • c) = r ^ p ^ f • (frobDR p R hR A)^[f] c := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GlobalTheory.LinFrob.frobDR_smul p hR, pow_succ,
      pow_mul]

private theorem pull_mem_span (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (g : A ⟶ A) (g' : A' ⟶ A') [IsMonHom g] [IsMonHom g']
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) {y : primDR A}
    (hy : y ∈ Submodule.span R (Set.range fun c => primPull (dp0 R) (𝟙 _) g ((frobDR p R hR A)^[f] c))) :
    (bcMor h).pull y ∈
      Submodule.span R' (Set.range fun c => primPull (dp0 R') (𝟙 _) g' ((frobDR p R' hR' A')^[f] c)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    refine Submodule.subset_span ⟨(bcMor h).pull c, ?_⟩
    simp only
    rw [pull_primPull h g g' hg, pull_frob_iter p hR hR' h]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ ha

private theorem no_up (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p R hR A e g f) : NO p R' hR' A' e' g' f := by
  intro x hx
  rw [(GlobalTheory.abelianDeRham.2.2.1 R A d hA hd R' A' φ h).2] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    rw [← pull_primPull h e e' he]
    exact pull_mem_span p hR hR' h g g' hg f (hN c hc)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

end SlopeTestRemainingChoices

section Down

open GlobalTheory.Published.AbelianDeRham

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Over (Sp K)} [GrpObj A]
  {A' : Over (Sp L)} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem mem_of_subtype_baseChange_eq_one_tmul {K L : Type} {V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (y : V) (s : L ⊗[K] W) (hs : (W.subtype.baseChange L) s = (1 : L) ⊗ₜ[K] y) : y ∈ W := by
  have hcomp : W.mkQ ∘ₗ W.subtype = 0 := by
    ext w
    exact (Submodule.Quotient.mk_eq_zero W).mpr w.2
  have hq : (W.mkQ.baseChange L) ((W.subtype.baseChange L) s) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [hs, LinearMap.baseChange_tmul] at hq
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (TensorProduct.lid K (V ⧸ W)) (LinearMap.rTensor (V ⧸ W) g ((1 : L) ⊗ₜ[K] W.mkQ y)) = 0 := by
    rw [hq, map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hg1, one_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2

set_option maxHeartbeats 200000 in

private theorem no_down (p : ℕ) [Fact p.Prime] (hK : (p : K) = 0) (hL : (p : L) = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap K L)) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p L hL A' e' g' f) : NO p K hK A e g f := by
  obtain ⟨-, -, hBC, -, -⟩ := GlobalTheory.abelianDeRham
  obtain ⟨hbij, hF⟩ := hBC K A d hA hd L A' φ h
  unfold NO at hN ⊢
  intro x hx
  have hPx : (bcMor h).pull x ∈ PrimitiveSubmodule A' := by
    rw [hF]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hy' := hN _ hPx
  rw [← pull_primPull h e e' he] at hy'
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span K
      (Set.range fun c => primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] c)) := ⟨_, rfl⟩
  rw [← hW]
  let Φ : L ⊗[K] W →ₗ[L] primDR A' := (liftSemi (bcMor h).pull).comp (W.subtype.baseChange L)
  have hΦ : ∀ (a : L) (w : W), Φ (a ⊗ₜ[K] w) = a • (bcMor h).pull (w : primDR A) := by
    intro a w
    simp only [Φ, LinearMap.comp_apply, LinearMap.baseChange_tmul, liftSemi_tmul, Submodule.subtype_apply]
  have hgen : ∀ t : L ⊗[K] primDR A,
      primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] (liftSemi (bcMor h).pull t)) ∈ LinearMap.range Φ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, iterate_map_zero, map_zero]
      exact Submodule.zero_mem _
    | tmul a v =>
      rw [liftSemi_tmul, frob_iter_smul p hL f a, ← pull_frob_iter p hK hL h f v, map_smul,
        ← pull_primPull h g g' hg]
      have hmem : primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] v) ∈ W := by
        rw [hW]
        exact Submodule.subset_span ⟨v, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(a ^ p ^ f) ⊗ₜ[K] (⟨_, hmem⟩ : W), hΦ _ _⟩
    | add t1 t2 h1 h2 =>
      rw [map_add, iterate_map_add, map_add]
      exact Submodule.add_mem _ h1 h2
  have hle : Submodule.span L (Set.range fun c => primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] c)) ≤
      LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨t, ht⟩ := hbij.2 c
    have h4 := hgen t
    rw [SetLike.mem_coe, ← ht]
    exact h4
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp (hle hy')
  simp only [Φ, LinearMap.comp_apply] at hs
  have h5 : liftSemi (bcMor h).pull (W.subtype.baseChange L s) =
      liftSemi (bcMor h).pull ((1 : L) ⊗ₜ[K] primPull (dp0 K) (𝟙 (Sp K)) e x) := by
    rw [liftSemi_tmul, one_smul]
    exact hs
  have h6 := hbij.1 h5
  exact mem_of_subtype_baseChange_eq_one_tmul W _ s h6

end Down

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.desc :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ) (π : Par p w f)
      (κ k T : Type) [Field κ] [Field k] [CommRing T] (hκ : (p : κ) = 0) (hk : (p : k) = 0) (hT : (p : T) = 0) (σ : κ →+* k) (τ : κ →+* T)
      (s : Sp κ ⟶ Sp R) (s₀ : Sp k ⟶ Sp R) (s' : Sp T ⟶ Sp R) (o : Obj b N s) (o₀ : Obj b N s₀) (o' : Obj b N s'),
      ObjMap o₀ o (spMap σ) → ObjMap o' o (spMap τ) → NOo hk o₀ π → NOo hT o' π := by
  intro p _ D R _ b N w f π κ k T _ _ _ hκ hk hT σ τ s s₀ s' o o₀ o' m₀ m' hN
  letI : Algebra κ k := σ.toAlgebra
  letI : Algebra κ T := τ.toAlgebra
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  have hd := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N _ s o
  have h1 : NOo hκ o π :=
    no_down p hκ hk m₀.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m₀.act _) (m₀.act _) f hN
  exact no_up p hκ hT m'.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m'.act _) (m'.act _) f h1
