import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OneLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem sub_dual (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ (P : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ P.asIdeal ↔ x.fst = 0 := by
    intro P x
    have hε : (DualNumber.eps : DualNumber k) ∈ P.asIdeal :=
      P.2.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact P.asIdeal.zero_mem)
    constructor
    · intro hx
      by_contra h0
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h0)
      exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h0
      have e : x = (TrivSqZeroExt.inl x.snd : DualNumber k) * DualNumber.eps := by
        apply TrivSqZeroExt.ext
        · rw [TrivSqZeroExt.fst_mul, h0, DualNumber.fst_eps, mul_zero]
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.snd_eps, DualNumber.fst_eps]
          simp
      rw [e]
      exact P.asIdeal.mul_mem_left _ hε
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun x => (key P x).trans (key Q x).symm)⟩

private theorem cancel_sp {k T : Type} [Field k] [CommRing T] (j : DualNumber k →+* T) (hj : Function.Injective j)
    {Y : Scheme.{0}} {g₁ g₂ : Sp (DualNumber k) ⟶ Y} (e : spMap j ≫ g₁ = spMap j ≫ g₂) : g₁ = g₂ := by
  haveI hs : Subsingleton (Sp (DualNumber k)) := sub_dual k
  haveI : Nontrivial T := hj.nontrivial
  obtain ⟨t⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  let x : Sp (DualNumber k) := spMap j t
  have hxy : g₁ x = g₂ x := by
    have := congrArg (fun g : Sp T ⟶ Y => g t) e
    simpa [x] using this
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := g₁ x) (U := ⊤) trivial
  have r1 : Set.range g₁ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x, Scheme.Opens.range_ι]
    exact hy
  have r2 : Set.range g₂ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x, ← hxy, Scheme.Opens.range_ι]
    exact hy
  haveI : IsAffine U.toScheme := hU
  have f₁ := IsOpenImmersion.lift_fac U.ι g₁ r1
  have f₂ := IsOpenImmersion.lift_fac U.ι g₂ r2
  set h₁ := IsOpenImmersion.lift U.ι g₁ r1
  set h₂ := IsOpenImmersion.lift U.ι g₂ r2
  have e' : spMap j ≫ h₁ = spMap j ≫ h₂ := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, f₁, f₂, e]
  have hm : Mono (Scheme.Hom.appTop (spMap j)) := by
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
    have hi : Mono (CommRingCat.ofHom j) := ConcreteCategory.mono_of_injective _ hj
    have : Mono (Scheme.Hom.appTop (spMap j) ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) := by
      change Mono (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom j)) ≫ _)
      rw [n]; exact mono_comp _ _
    exact mono_of_mono _ (Scheme.ΓSpecIso (CommRingCat.of T)).hom
  have hh : h₁ = h₂ := by
    apply ext_of_isAffine
    rw [← cancel_mono (Scheme.Hom.appTop (spMap j))]
    have := congrArg Scheme.Hom.appTop e'
    simpa using this
  rw [← f₁, ← f₂, hh]

private theorem frobN_nat {X Y : Scheme.{0}} (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (g : Y ⟶ X) (f : ℕ) :
    frobN p Y hY f ≫ g = g ≫ frobN p X hX f := by
  induction f with
  | zero => simp [frobN]
  | succ n ih =>
    simp only [frobN, Category.assoc, ih]
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p hX g hY, Category.assoc]

private theorem frobN_sp (T : Type) [CommRing T] (hT : (p : T) = 0) (h : (p : Γ(Sp T, ⊤)) = 0) (f : ℕ) :
    ∃ φ : T →+* T, (∀ x, φ x = x ^ p ^ f) ∧ frobN p (Sp T) h f = spMap φ := by
  induction f with
  | zero => exact ⟨RingHom.id T, fun x => by simp, by rw [frobN]; exact (spMap_id T).symm⟩
  | succ n ih =>
    obtain ⟨φ, h1, h2⟩ := ih
    refine ⟨(frobR p T hT).comp φ, fun x => ?_, ?_⟩
    · rw [RingHom.comp_apply, frobR_apply, h1, pow_succ, pow_mul]
    · rw [frobN, h2, frob_sp p T hT h, GlobalTheory.Cris.spMap_comp]

end UpperTheory.Gal.Ord.HasseL

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem const_of {k : Type} [Field k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (ψ : A.left ⟶ A.left)
    (a : A ⟶ A) [IsMonHom a] (f : ℕ) (ha : frobN p A.left (cast_left p k hk A) f ≫ ψ = a.left)
    {T : Type} [CommRing T] [Algebra k T] (τ : T →ₐ[k] DualNumber k) (j : DualNumber k →+* T)
    (u : Over.mk (spMap (algebraMap k T)) ⟶ A) (hj : Function.Injective j) (hq : ∀ x, j (τ x) = x ^ p ^ f)
    (hu : u ≫ a = 1) (v : epsR k ⟶ A) (hv : IsTangent v) (hτ : spMap (τ : T →+* DualNumber k) ≫ u.left = v.left) :
    IsConst (v.left ≫ ψ) := by
  have hT : (p : T) = 0 := by
    have := congrArg (algebraMap k T) hk
    simpa using this
  have hXT := cast_left p T hT (Over.mk (𝟙 (Sp T)))
  have hXk := cast_left p k hk (Over.mk (𝟙 (Sp k)))
  have hA := cast_left p k hk A
  obtain ⟨φ, hφ1, hφ2⟩ := frobN_sp (p := p) T hT hXT f
  obtain ⟨φk, hk1, hk2⟩ := frobN_sp (p := p) k hk hXk f
  have hjτ : φ = j.comp (τ : T →+* DualNumber k) := RingHom.ext fun x => by
    rw [hφ1, RingHom.comp_apply]; exact (hq x).symm
  have hone : (1 : Over.mk (spMap (algebraMap k T)) ⟶ A).left = spMap (algebraMap k T) ≫ η[A].left := by
    simp [Hom.one_def]

  have hR : spMap j ≫ v.left ≫ ψ = spMap (algebraMap k T) ≫ η[A].left := by
    have e1 : spMap j ≫ v.left = u.left ≫ frobN p A.left hA f := by
      rw [← hτ, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← hjτ, ← hφ2]
      exact frobN_nat hA hXT u.left f
    rw [← Category.assoc, e1, Category.assoc, ha, ← Over.comp_left, hu, hone]

  have hL : spMap j ≫ spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v.left ≫ ψ =
      spMap (algebraMap k T) ≫ η[A].left := by
    have c : j.comp (algebraMap k (DualNumber k)) = (algebraMap k T).comp φk := RingHom.ext fun c => by
      have := hq (algebraMap k T c)
      rw [AlgHom.commutes] at this
      rw [RingHom.comp_apply, this, RingHom.comp_apply, hk1, map_pow]
    have e0 : η[A].left ≫ frobN p A.left hA f = frobN p (Sp k) hXk f ≫ η[A].left :=
      (frobN_nat hA hXk η[A].left f).symm
    have e2 : η[A].left ≫ a.left = η[A].left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    have e3 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = η[A].left := hv
    have e4 : spMap j ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k T) ≫ spMap φk := by
      rw [← GlobalTheory.Cris.spMap_comp, c, GlobalTheory.Cris.spMap_comp]
    have e5 : spMap φk ≫ η[A].left ≫ ψ = η[A].left := by
      rw [← hk2, ← Category.assoc, ← e0, Category.assoc, ha, e2]
    have e6 : spMap j ≫ spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v.left ≫ ψ =
        (spMap j ≫ spMap (algebraMap k (DualNumber k))) ≫ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left) ≫ ψ := by
      rw [GlobalTheory.Cris.spMap_comp]
      simp only [Category.assoc]
    rw [e6, e3, e4, Category.assoc, e5]
  exact cancel_sp j hj (by rw [hL, hR])

end UpperTheory.Gal.Ord.HasseL

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem eps_pull {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (m : SMor A σ ψ) (E : A ⟶ A) [IsMonHom E] (e : ψ ≫ E.left = E.left ≫ ψ) (h : HdR A) (x : primDR A) :
    h (m.pull (primPull (dp0 k) (𝟙 _) E x)) = push (dp0 k) (𝟙 _) E h (m.pull x) := by
  rw [push_apply]
  have c := (homMor (dp0 k) (𝟙 _) E).comp m
  have e1 : primPull (dp0 k) (𝟙 _) E (m.pull x) = c.pull x :=
    GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) E) c (fun _ ↦ rfl) e.symm x
  have e2 : m.pull (primPull (dp0 k) (𝟙 _) E x) = c.pull x :=
    GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) E) m c (fun _ ↦ rfl) rfl x
  rw [e1, e2]

private theorem pullback_first_filtration_primitive {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (m : SMor A σ ψ) {x : primDR A} (hx : x ∈ PrimitiveSubmodule A) : m.pull x ∈ PrimitiveSubmodule A :=
  m.isMor.pullback1_mem_hodgeFiltration hx

end UpperTheory.Gal.Ord.HasseL

open UpperTheory.Gal.Ord.HasseL in
theorem UpperTheory.Gal.Ord.hasse :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : o.A.left ⟶ o.A.left) (m : SMor o.A σ ψ), frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left →
      ∀ v : epsR k ⟶ o.A, IsTangent v → v ≠ 1 → IsDeep o w (p ^ f) v → ∀ x ∈ PrimitiveSubmodule o.A, m.pull (coh o π.ε x) = 0 := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hnorm hf π σ hσ ψ m ha v hv hv1 hdeep x hx
  obtain ⟨T, _, _, τ, j, u, hj, hq, hku, hτ⟩ := hdeep
  have hab := o.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension k o.A hab
  have HL : LieExact o.A := GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    GlobalTheory.AbCoh.abelianHodgeDeRham k o.A g hab hg
  haveI := hab.smooth
  haveI : AlgebraicGeometry.IsReduced o.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced o.A.hom
  have hA := cast_left p k hk o.A
  haveI hEm : IsMonHom (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)) := o.act.hom _
  haveI hAm : IsMonHom (o.act.act (algebraMap (𝓞 D.F) D.O π.a)) := o.act.hom _

  have hconst : IsConst (v.left ≫ ψ) :=
    const_of hk o.A ψ (o.act.act (algebraMap (𝓞 D.F) D.O π.a)) f ha τ j u hj hq (hku _ π.mem) v hv hτ
  obtain ⟨h₁, hl₁⟩ := HL.2 v hv
  have hforms := (UpperTheory.Gal.Ord.tan k o.A hab σ ψ m hσ.2 v hv).2 hconst
  have hz₁ : ∀ z ∈ PrimitiveSubmodule o.A, h₁ (m.pull z) = 0 := by
    rintro ⟨c, hc⟩ hzF
    have hc' : c ∈ F1 (o.A.hom ≫ 𝟙 _) := hzF
    rw [hodgeFiltration_eq_range] at hc'
    obtain ⟨fm, rfl⟩ := hc'
    have hp : Form.cl _ (m.isMor.pullForm fm) ∈ primDR o.A := by
      rw [IsMor.cl_pullForm]
      exact m.pullback_mem_primitive hc
    have e : m.pull ⟨_, hc⟩ = ⟨_, hp⟩ := Subtype.ext (IsMor.cl_pullForm _ _).symm
    rw [e, hl₁.2, hforms fm hc]

  let τ' : epsR k ⟶ Over.mk (spMap (algebraMap k T)) := Over.homMk (spMap (τ : T →+* DualNumber k)) (by
    simp only [Over.mk_hom]
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact τ.comp_algebraMap)
  have hvτ : v = τ' ≫ u := Over.OverMorphism.ext (by simpa [τ'] using hτ.symm)
  have hkill : ∀ c ∈ w, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    rw [hvτ, Category.assoc, hku c hc, MonObj.comp_one]
  have hvE : v ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.ε) = v := by
    have e : o.act.act (algebraMap (𝓞 D.F) D.O π.ε) = o.act.act (algebraMap (𝓞 D.F) D.O (π.ε - 1)) * 𝟙 o.A := by
      rw [← o.act.one, ← o.act.add, ← map_one (algebraMap (𝓞 D.F) D.O), ← map_add, sub_add_cancel]
    rw [e, MonObj.comp_mul, hkill _ π.one, Category.comp_id, _root_.one_mul]
  have hlE : IsLieImage (hom o π.ε h₁) v := by
    have := hl₁.push (o.act.act (algebraMap (𝓞 D.F) D.O π.ε))
    rw [hvE] at this
    exact this
  have hd₁ : hom o π.ε h₁ - h₁ ∈ Fil o.A := hlE.sub_mem hl₁
  have hn₁ : h₁ ∉ Fil o.A := fun hh => hv1 ((HL.1 h₁).unique hl₁ (isLieImage_one_iff.2 hh))
  obtain ⟨-, ⟨h₀, -, hall⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  obtain ⟨l₀, hl₀⟩ := hall h₁
  have hd₀ : h₁ - l₀ • hom o π.ε h₀ ∈ Fil o.A := by
    have := Submodule.sub_mem _ hl₀ hd₁
    have e : hom o π.ε h₁ - l₀ • hom o π.ε h₀ - (hom o π.ε h₁ - h₁) = h₁ - l₀ • hom o π.ε h₀ := by abel
    rwa [e] at this
  have hne : l₀ ≠ 0 := fun e => hn₁ (by simpa [e] using hd₀)

  have hcomm : ψ ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left = (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left ≫ ψ := by
    haveI := (UpperTheory.Gal.Ord.epi p o.A.left hA).2 f
    rw [← cancel_epi (frobN p o.A.left hA f), ← Category.assoc, ha, ← Category.assoc,
      frobN_nat hA hA (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left f, Category.assoc, ha,
      ← Over.comp_left, ← Over.comp_left, ← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]
  have hz : ∀ z ∈ PrimitiveSubmodule o.A, hom o π.ε h₀ (m.pull z) = 0 := fun z hzF => by
    have e := (Submodule.mem_dualAnnihilator _).1 hd₀ _ (pullback_first_filtration_primitive m hzF)
    rw [LinearMap.sub_apply, hz₁ z hzF, LinearMap.smul_apply, zero_sub, neg_eq_zero, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun h => ?_
  obtain ⟨l, hl⟩ := hall h
  have e1 : h (m.pull (coh o π.ε x)) = hom o π.ε h (m.pull x) :=
    eps_pull m (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)) hcomm h x
  have e2 := (Submodule.mem_dualAnnihilator _).1 hl _ (pullback_first_filtration_primitive m hx)
  rw [LinearMap.sub_apply, LinearMap.smul_apply, hz x hx, smul_zero, sub_zero] at e2
  rw [e1, e2]
