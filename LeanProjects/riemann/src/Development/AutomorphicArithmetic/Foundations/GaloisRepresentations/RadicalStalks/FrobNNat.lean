import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem frobN_nat (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}} (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    (φ : Y ⟶ X) (j : ℕ) : frobN p Y hY j ≫ φ = φ ≫ frobN p X hX j := by
  induction j with
  | zero => simp [frobN]
  | succ j ih =>
    simp only [frobN, Category.assoc, ih]
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p hX φ hY, Category.assoc]

private theorem rel_mor (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (f : ℕ) (hf : 0 < f)
    (ψ V g c a q : X ⟶ X) (h1 : frobN p X h f ≫ ψ = a) (h2 : GlobalTheory.VB.frob X p h ≫ V = q) (h3 : a ≫ g = q ≫ c) :
    ψ ≫ frobN p X h (f - 1) ≫ g = V ≫ c := by
  haveI := (UpperTheory.Gal.Ord.epi p X h).2 f
  rw [← cancel_epi (frobN p X h f)]
  obtain ⟨j, rfl⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
  have e : frobN p X h (j + 1) = frobN p X h j ≫ GlobalTheory.VB.frob X p h :=
    frobN_nat p h h (GlobalTheory.VB.frob X p h) j |>.symm ▸ rfl
  calc frobN p X h (j + 1) ≫ ψ ≫ frobN p X h (j + 1 - 1) ≫ g
      = (frobN p X h (j + 1) ≫ ψ) ≫ frobN p X h j ≫ g := by simp
    _ = frobN p X h j ≫ a ≫ g := by
        rw [h1, ← Category.assoc, ← frobN_nat p h h a j, Category.assoc]
    _ = frobN p X h j ≫ (GlobalTheory.VB.frob X p h ≫ V) ≫ c := by rw [h3, h2]
    _ = frobN p X h (j + 1) ≫ V ≫ c := by rw [e]; simp

private theorem frobN_mor (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (j : ℕ) :
    ∃ (ρ : k →+* k) (u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ρ (spMap ρ) (frobN p A.left (cast_left p k hk A) j)),
      ∀ c, u.pull c = (frobDR p k hk A)^[j] c := by
  induction j with
  | zero =>
    have u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A (RingHom.id k) (spMap (RingHom.id k)) (frobN p A.left (cast_left p k hk A) 0) := by
      rw [GlobalTheory.Cris.spMap_id]
      exact homMor (dp0 k) (𝟙 _) (𝟙 A)
    exact ⟨RingHom.id k, u, fun c ↦ Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)⟩
  | succ j ih =>
    obtain ⟨ρ, u, hu⟩ := ih
    have F := frobMor p k hk A (cast_left p k hk A)
    have K : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ((frobR p k hk).comp ρ) (spMap ((frobR p k hk).comp ρ))
        (frobN p A.left (cast_left p k hk A) (j + 1)) := by
      rw [GlobalTheory.SchRing.spMap_comp']
      exact u.comp F
    refine ⟨_, K, fun c ↦ ?_⟩
    rw [Function.iterate_succ_apply', ← hu]
    exact (GrpMor.pull_pull u F K (fun _ ↦ rfl) rfl c).symm

private theorem act_nat {O : Type} [Ring O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OActN O G) (n : ℕ) :
    a.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have := a.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.rel :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ (σ τ : k →+* k) (ψ V : o.A.left ⟶ o.A.left) (m : SMor o.A σ ψ) (n : SMor o.A τ V), frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left →
      GlobalTheory.VB.frob o.A.left p (cast_left p k hk o.A) ≫ V = ((𝟙 o.A) ^ p : o.A ⟶ o.A).left →
      ∀ y, m.pull ((frobDR p k hk o.A)^[f - 1] (coh o π.g y)) = n.pull (coh o π.c y) := by
  intro p _ D R _ b N _ _ _ k _ _ hk β o i w f _ _ hf π σ τ ψ V m n h1 h2 y
  haveI hg := o.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI hc := o.act.hom (algebraMap (𝓞 D.F) D.O π.c)
  haveI : Smooth o.A.hom := o.ab.smooth
  haveI : IsReduced o.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced o.A.hom
  obtain ⟨ρ, u, hu⟩ := frobN_mor p hk o.A (f - 1)
  have gm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.g))
  have cm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.c))
  have h3 : o.act.act (algebraMap (𝓞 D.F) D.O π.a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.g) =
      ((𝟙 o.A) ^ p : o.A ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.c) := by
    rw [← act_nat o.act p, ← o.act.mul, ← o.act.mul]
    congr 1
    rw [← map_mul, ← map_natCast (algebraMap (𝓞 D.F) D.O) p, ← map_mul, mul_comm π.g, π.prod, mul_comm]
  have hmor := rel_mor p (cast_left p k hk o.A) f hf ψ V _ _ _ _ h1 h2 (congrArg (·.left) h3)
  have K1 := gm.comp u
  have K2 := cm.comp n
  have hring : σ.comp ρ = τ := by
    have e1 : (ψ ≫ frobN p o.A.left (cast_left p k hk o.A) (f - 1) ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.g)).left) ≫ o.A.hom =
        o.A.hom ≫ spMap σ ≫ spMap ρ := by
      rw [Category.assoc, Category.assoc, Over.w, u.w, ← Category.assoc, m.w, Category.assoc]
    have e2 : (V ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.c)).left) ≫ o.A.hom = o.A.hom ≫ spMap τ := by
      rw [Category.assoc, Over.w, n.w]
    have e3 : o.A.hom ≫ spMap σ ≫ spMap ρ = o.A.hom ≫ spMap τ :=
      e1.symm.trans ((congrArg (· ≫ o.A.hom) hmor).trans e2)
    have e := (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ o.A)
    have e4 : e.left ≫ o.A.hom = 𝟙 _ := Over.w e
    have e5 : spMap σ ≫ spMap ρ = spMap τ := by
      have := congrArg (e.left ≫ ·) e3
      simpa only [← Category.assoc, e4, Category.id_comp] using this
    apply GlobalTheory.SchRing.spMap_inj
    rw [GlobalTheory.SchRing.spMap_comp']
    exact e5
  rw [← hu]
  exact (congrArg m.pull (GrpMor.pull_pull gm u K1 (fun _ ↦ rfl) rfl y)).trans
    ((GrpMor.pull_pull K1 m K2 (fun r ↦ DFunLike.congr_fun hring r) hmor y).trans
      (GrpMor.pull_pull cm n K2 (fun _ ↦ rfl) rfl y).symm)
