import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ResPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairPullback

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ot_inv {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') (hi : Function.Injective e.p) :
    ∃ k : G'.Hom G, ∀ g, k.p (e.p g) = g := by
  let eq : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hi, e.surj⟩
  have hk : ∀ x, e.p (eq.symm x) = x := fun x => eq.apply_symm_apply x
  have hcont : Continuous (eq.symm : G'.Γ → G.Γ) :=
    (Continuous.homeoOfEquivCompactToT2 (f := eq.toEquiv) e.cont).symm.continuous
  refine ⟨Glob.Hom.mk eq.symm.toMonoidHom hcont eq.symm.surjective (fun g => ?_) ?_ (fun g => ?_)
    (fun v g => ?_) (fun v g => ?_), fun g => eq.symm_apply_apply g⟩
  · show G.η (eq.symm g) = G'.η g
    rw [← e.η, hk]
  · show eq.symm G'.c = G.c
    apply hi
    rw [hk, e.c]
  · show G.ε (eq.symm g) = G'.ε g
    rw [← e.ε, hk]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φ]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φu]

private theorem ot_tr_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (y : MonoidAlgebra A H) : (D.comap φ).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have key : ∀ z : MonoidAlgebra A H, MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m r => simp [MonoidAlgebra.mapRingHom_single]
  show (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C y))).coeff (n - 1) =
    (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ y))).coeff (n - 1)
  rw [map_sub, key]
  simp

private theorem ot_comap_comap {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (D : GDet n A G)
    (φ : H →* G) (ψ : K →* H) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) (MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.mapDomainRingHom B ψ x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (φ.comp ψ) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem ot_single {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (a : A) :
    MonoidAlgebra.mapDomainRingHom A φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by simp

private theorem mapDomain_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (u : Fin n → A) :
    MonoidAlgebra.mapDomainRingHom A φ (q1El g u) = q1El (φ g) u := by
  simp only [q1El, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, map_one]

private theorem mapDomain_partial_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g t : H) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapDomainRingHom A φ (q2El g t u i y) = q2El (φ g) (φ t) u i y := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, apply_ite,
    map_one]

private theorem ot_pair {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (k : G'.Hom G) {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid G.frame O n} {r' : Resid G'.frame O n} (hc : Glob.Compat k r' r)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) :
    ∃ p' : Pair r' R, p'.D = p.D.comap k.p₀ ∧ p'.ψ = p.ψ := by
  let fh : FHom G'.frame G.frame :=
    { π := k.p, π_cont := k.cont, hη := k.η, hc := k.c, hε := k.ε, vl := id,
      gv := fun _ => MonoidHom.id _, gv_cont := fun _ => continuous_id,
      hφ := fun v g => (k.φ v g).symm, hI := fun _ _ hg => hg }
  have hπ : fh.π₀ = k.p₀ := rfl
  obtain ⟨h1, h2, h3⟩ := hc
  have hfc : fh.Compat r' r := by
    refine ⟨fun i => by rw [hπ]; exact h1 i, fun v i => ?_, fun v i g hg => ?_, fun u g hg => ?_⟩
    · rw [h2]
      rfl
    · rw [h3]
      rfl
    · right
      refine ⟨u, ?_⟩
      obtain ⟨hgI, hgk⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgI
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        exact Subtype.ext (k.φu u x).symm
      · rw [Subgroup.mem_iInf] at hgk ⊢
        intro i
        have := hgk i
        rw [MonoidHom.mem_ker, h1 i] at this
        rw [MonoidHom.mem_ker, hπ]
        exact this
  obtain ⟨p', hD, hψ⟩ := exists_determinantPair_pullback l G'.frame G.frame fh O n r' r hfc
    (fun h0 => (p.isEmpty_of_zero h0).1) R p
  exact ⟨p', hD, funext fun v => funext fun i => by rw [hψ]; rfl⟩

theorem UpperTheory.V.Pa.Lev.opTransport :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G G' : Glob l L) (e : G.Hom G') (h : G.Hom G0) (h' : G'.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ), Function.Injective e.p → (∀ g, h'.p (e.p g) = h.p g) → OpRel A Nq ph ta ex → ∃ A' : OpMod b h' q N, OpRel A' Nq (fun j => e.p₀ (ph j)) (fun j => e.p₀ (ta j)) ex := by
  intro l _ L G0 O _ _ _ _ _ n r B _ _ _ u J D b G G' e h h' q N A Nq ph ta ex hi hh hR
  obtain ⟨k, hk⟩ := ot_inv e hi
  have hek : ∀ x, e.p (k.p x) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surj x
    rw [hk]
  have hcomp : h.p₀.comp k.p₀ = h'.p₀ := MonoidHom.ext fun g => Subtype.ext (by
    show h.p (k.p (g : G'.Γ)) = h'.p (g : G'.Γ)
    rw [← hh, hek])
  have hpe : ∀ x, h'.p₀ (e.p₀ x) = h.p₀ x := fun x => Subtype.ext (hh (x : G.Γ))
  have hke : ∀ x, k.p₀ (e.p₀ x) = x := fun x => Subtype.ext (hk (x : G.Γ))
  obtain ⟨rN', hc'⟩ := Core.resPull l L G' G0 h' n O r
  have hck : Glob.Compat k rN' A.rN := by
    obtain ⟨h1, h2, h3⟩ := hc'
    obtain ⟨a1, a2, a3⟩ := A.compat
    refine ⟨fun i => ?_, h2.trans a2.symm, h3.trans a3.symm⟩
    rw [h1 i, a1 i, MonoidHom.comp_assoc, hcomp]
  obtain ⟨p', hpD, hpψ⟩ := ot_pair k hck A.p
  have hmc : ∀ {S : Type} [CommRing S] (f : A.R →+* S), (A.p.D.comap k.p₀).map f = (A.p.D.map f).comap k.p₀ :=
    fun _ => rfl
  have hlam : ∀ j : Fin D, (algebraMap (abelian₂ O Empty D) A.R) (MvPowerSeries.X (Sum.inr j)) =
      (algebraMap O A.R) (b.wt.c j) * ↑((p'.ψ (b.wt.v j) (b.wt.i j)) (b.wt.γ j)) - 1 := by
    intro j
    rw [hpψ]
    exact A.segmentWeightExponent j
  have hβ : p'.Maps A.β.toRingHom (u.D.comap h'.p₀) u.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · rw [hpD, hmc, A.β_pair.1, ot_comap_comap, hcomp]
    · rw [hpψ]
      exact A.β_pair.2 v i
  refine ⟨{ A with
              rN := rN'
              compat := hc'
              p := p'
              segmentWeightExponent := hlam
              β_pair := hβ }, ?_⟩
  refine ⟨?_, fun j g => ?_, fun j i g => ?_⟩
  · dsimp only
    simp only [hpe]
    exact hR.two
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_charpoly_element]
    simp only [hke]
    exact hR.rel1 j (k.p₀ g)
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_partial_charpoly_element]
    simp only [hke]
    exact hR.rel2 j i (k.p₀ g)
