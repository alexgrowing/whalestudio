import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead

variable {D : D7}

def IdFrame {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∃ hn : V.rank = n, ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

variable {S T : HSp D} {n : ℕ}

def RatMatch (φ : GAf D.host.E n ≃* Bridge.Gf S) : Prop :=
  (∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, ∃ γ', Bridge.ratF S γ' = φ γ) ∧
    ∀ γ', ∃ γ : ReciprocityTheory.Aut.GQ D.host.E n, Bridge.ratF S γ' = φ γ

def WtMap (B : Base S T) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (ω : W →ₛₗ[e] PolF D T.rank S.rank) : Prop :=
  Function.Injective ω ∧ (∀ w, ω w ∈ B.valSpace) ∧
    (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ S), Bridge.ratF S γ' = φ γ →
      ∀ w, ω (ρ γ w) = B.act (γ' : GA D S) (ω w)) ∧
    (∀ h, ∀ x ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h, x ∈ Set.range ω) ∧
    ∀ h w, ∃ c : R, c ≠ 0 ∧
      ω (algebraMap R (FractionRing R) c • w) ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h

def LevMatch (B : Base S T) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) {K : Type} [Field K] (e : K →+* ℂ)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* Kˣ) : Prop :=
  (∀ g, g ∈ J ↔ φ g ∈ B.levJ t) ∧
    ∀ g (h : g ∈ J) (h' : φ g ∈ B.levJ t), e ((χ ⟨g, h⟩ : Kˣ) : K) = ((B.levLam t ⟨φ g, h'⟩ : ℂˣ) : ℂ)

theorem finite_kP (P : Pl D.host.E) : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

theorem isOfFinOrder_levFn {m : ℕ} (β : GL (Fin m) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ m) (x : GL (Fin m) (Lev.EAf D)) :
    IsOfFinOrder (levFn β L x) := by
  haveI : ∀ P : Pl D.host.E, Finite (kP P) := finite_kP
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℂˣ), (∀ i ∈ s, IsOfFinOrder (f i)) → IsOfFinOrder (∏ i ∈ s, f i) :=
    fun s f h => Finset.prod_induction f IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one h
  unfold levFn
  refine (IsOfFinOrder.mul ?_ (hprod _ _ fun P _ => hprod _ _ fun c _ => ?_)).mul (hprod _ _ fun P _ => ?_)
  · unfold ext1
    split_ifs with h
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact IsOfFinOrder.one
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

theorem mem_range_of_finOrder {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    {x : FractionRing R} {z : ℂˣ} (hz : IsOfFinOrder z) (h : e x = z) : (z : ℂ) ∈ (e.comp (algebraMap R (FractionRing R))).range := by
  obtain ⟨m, hm, h1⟩ := hz.exists_pow_eq_one
  have h2 : x ^ m = 1 := e.injective (by rw [map_pow, h, ← Units.val_pow_eq_pow_val, h1, map_one, Units.val_one])
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := R) hm (h2 ▸ isIntegral_one))
  exact ⟨y, by rw [RingHom.comp_apply, hy, h]⟩

theorem read_abstract {G G' Γ' R W P I V : Type} [Group G] [Group G'] [Group Γ'] [CommRing R] [IsDomain R] [AddCommGroup W]
    [Module (FractionRing R) W] [AddCommGroup P] [Module ℂ P] [Finite I] [AddCommGroup V] [Module (FractionRing R) V]
    (φ : G ≃* G') (Γ J : Subgroup G) (J' : Subgroup G') (ι : Γ' → G') (e : FractionRing R →+* ℂ) (ρ : Γ → W → W) (χ : J → FractionRing R)
    (act : Γ' → P → P) (lam : J' → ℂ) (ω : W →ₛₗ[e] P) (val : Set P)
    (L : G' → Submodule (e.comp (algebraMap R (FractionRing R))).range P)
    (A : Submodule (FractionRing R) (G → W))
    (hA : ∀ f, f ∈ A ↔ (∀ (γ : Γ) g, f (γ * g) = ρ γ (f g)) ∧ ∀ (κ : J) g, f (g * κ) = χ κ • f g)
    (M : Set (G' → P))
    (hM : ∀ F, F ∈ M ↔ ((∀ h, F h ∈ val) ∧ ∀ γ h (k : J'), F (ι γ * h * k) = lam k • act γ (F h)) ∧ ∀ h, F h ∈ L h)
    (h1 : ∃ γ, ι γ = 1 ∧ ∀ x, act γ x = x) (hl1 : lam 1 = 1)
    (hr1 : ∀ γ : Γ, ∃ γ', ι γ' = φ γ) (hr2 : ∀ γ', ∃ γ : Γ, ι γ' = φ γ)
    (hinj : Function.Injective ω) (hval : ∀ w, ω w ∈ val) (heq : ∀ (γ : Γ) γ', ι γ' = φ γ → ∀ w, ω (ρ γ w) = act γ' (ω w))
    (hrange : ∀ h, ∀ x ∈ L h, x ∈ Set.range ω) (hden : ∀ h w, ∃ c : R, c ≠ 0 ∧ ω (algebraMap R (FractionRing R) c • w) ∈ L h)
    (hJ1 : ∀ g, g ∈ J ↔ φ g ∈ J') (hJ2 : ∀ g (h : g ∈ J) (h' : φ g ∈ J'), e (χ ⟨g, h⟩) = lam ⟨φ g, h'⟩)
    (hlam : ∀ k, lam k ∈ (e.comp (algebraMap R (FractionRing R))).range)
    (hact : ∀ γ h (k : J'), ∀ x ∈ L h, act γ x ∈ L (ι γ * h * k))
    (y : I → G') (hy : ∀ h, ∃ i γ, ∃ k : J', h = ι γ * y i * k) (real : V ≃ₗ[FractionRing R] A) :
    ∃ r : V →ₛₗ[e] (G' → P), Function.Injective r ∧ (∀ F ∈ M, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R) {f | r f ∈ M} = ⊤ ∧ ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  let r : V →ₛₗ[e] (G' → P) :=
    { toFun := fun f h => ω ((real f).1 (φ.symm h))
      map_add' := fun f f' => by funext h; simp
      map_smul' := fun c f => by funext h; simp [map_smulₛₗ] }
  have hr_apply : ∀ f g, r f (φ g) = ω ((real f).1 g) := fun f g => by
    change ω ((real f).1 (φ.symm (φ g))) = _
    rw [φ.symm_apply_apply]
  have hlaw : ∀ f γ h (k : J'), r f (ι γ * h * k) = lam k • act γ (r f h) := fun f γ' h k => by
    obtain ⟨γ, hγ⟩ := hr2 γ'
    obtain ⟨g, rfl⟩ := φ.surjective h
    obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    have hκ := (hJ1 κ).2 hk
    change r f (ι γ' * φ g * φ κ) = _
    have h2 := (hA _).1 (real f).2
    rw [hγ, ← map_mul, ← map_mul, hr_apply, hr_apply, h2.2 ⟨κ, hκ⟩, h2.1, map_smulₛₗ, heq γ γ' hγ, hJ2 κ hκ hk]
  refine ⟨r, fun f f' h => ?_, fun F hF => ?_, ?_, hr_apply⟩
  · refine real.injective (Subtype.ext (funext fun g => hinj ?_))
    rw [← hr_apply, ← hr_apply, h]
  · obtain ⟨⟨-, hF3⟩, hF2⟩ := (hM F).1 hF
    choose u hu using fun g => hrange (φ g) _ (hF2 (φ g))
    have hmem : u ∈ A := by
      refine (hA u).2 ⟨fun γ g => hinj ?_, fun κ g => hinj ?_⟩
      · obtain ⟨γ', hγ⟩ := hr1 γ
        have := hF3 γ' (φ g) 1
        rw [heq γ γ' hγ, hu, hu, map_mul, ← hγ]
        simpa [hl1] using this
      · have hk := (hJ1 κ).1 κ.2
        obtain ⟨γ, hγ, hγ'⟩ := h1
        have := hF3 γ (φ g) ⟨φ κ, hk⟩
        rw [map_smulₛₗ, hu, hu, map_mul, hJ2 κ κ.2 hk]
        simpa [hγ, hγ'] using this
    refine ⟨real.symm ⟨u, hmem⟩, funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective h
    rw [hr_apply, real.apply_symm_apply, hu]
  · refine eq_top_iff.2 fun f _ => ?_
    haveI := Fintype.ofFinite I
    classical
    choose c hc0 hcm using fun i => hden (y i) ((real f).1 (φ.symm (y i)))
    have hd : algebraMap R (FractionRing R) (∏ i, c i) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
    have hm : r (algebraMap R (FractionRing R) (∏ i, c i) • f) ∈ M := by
      refine (hM _).2 ⟨⟨fun h => hval _, hlaw _⟩, fun h => ?_⟩
      obtain ⟨i, γ, k, rfl⟩ := hy h
      have e1 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) =
          e (algebraMap R (FractionRing R) (∏ j ∈ Finset.univ.erase i, c j)) •
            ω (algebraMap R (FractionRing R) (c i) • (real f).1 (φ.symm (y i))) := by
        rw [← map_smulₛₗ, smul_smul, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        change ω ((real (_ • f)).1 _) = _
        rw [map_smul]
        rfl
      have h2 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) ∈ L (y i) := by
        rw [e1]
        exact Submodule.smul_mem _ (⟨_, _, rfl⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hcm i)
      rw [hlaw]
      exact Submodule.smul_mem _ (⟨_, hlam k⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hact γ _ k _ h2)
    have := Submodule.smul_mem _ (algebraMap R (FractionRing R) (∏ i, c i))⁻¹ (Submodule.subset_span (R := FractionRing R)
      (s := {f | r f ∈ M}) hm)
    rwa [inv_smul_smul₀ hd] at this

theorem read_cell (B : Base S T) (hB : B.Good) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    (hc : IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* (FractionRing R)ˣ) (ω : W →ₛₗ[e] PolF D T.rank S.rank)
    (hr : RatMatch φ) (hω : WtMap B φ R e ρ ω) (hJ : LevMatch B t φ e J χ) {I : Type} [Finite I] (y : I → Bridge.Gf S)
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {V : Type} [AddCommGroup V] [Module (FractionRing R) V]
    (real : V ≃ₗ[FractionRing R] NX.TypeSpF D.host.E n (FractionRing R) ρ J χ) :
    ∃ r : V →ₛₗ[e] (Bridge.Gf S → PolF D T.rank S.rank), Function.Injective r ∧
      (∀ F ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R)
        {f | r f ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t} = ⊤ ∧
      ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  refine read_abstract φ (ReciprocityTheory.Aut.GQ D.host.E n) J (B.levJ t) (Bridge.ratF S) e (fun γ => ρ γ) (fun κ => (χ κ : FractionRing R))
    (fun γ => B.act (γ : GA D S)) (fun k => ((B.levLam t k : ℂˣ) : ℂ)) ω B.valSpace
    (B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range) _ (fun _ => Iff.rfl) _
    (fun F => (B.mem_mtLat _ _ _).trans (and_congr_left' B.mem_formsC)) ⟨1, MonoidHom.map_one _, fun x => ?_⟩ ?_ hr.1 hr.2
    hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2 hJ.1 hJ.2 (fun k => ?_)
    (fun γ h k x hx => Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hx) y
    (fun h => (hy h).exists.imp fun _ h => h) real
  · change B.act 1 x = x
    rw [MonoidHom.map_one]
    rfl
  · change ((B.levLam t 1 : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_one]
    rfl
  · obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    exact mem_range_of_finOrder e (isOfFinOrder_levFn _ _ _) (hJ.2 κ ((hJ.1 κ).2 hk) hk)

theorem admissible_twist_of_twisting_character {i : D.ntw.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : NX.AdmTw D i k Q ψ := by
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := h
  have hS : ∀ P ∈ Q, P ∉ D.ntw.S0 i := fun P hP => Finset.disjoint_left.1 hdisj hP
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  refine ⟨fun P hP => ⟨hsplit P hP, fun h => hS P hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)⟩,
    fun P hP => ⟨fun h => hS P hP (D.ntw.primes_subset_exceptional i h), fun k' h => hS P hP (D.ntw.placesOver_subset_exceptional i k' h)⟩, hopen, hanti, fun σ => ⟨k, ?_⟩,
    fun P hP A hA σ hσ => ?_⟩
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · by_contra h
    exact hP ((hram P A hA).1 ⟨σ, hσ, h⟩)

theorem eq_of_infOf_eq {m : ℕ} {a b : Fin m → ℤ} (ha : Antitone a) (hb : Antitone b) (h : NG.infOf a = NG.infOf b) : a = b := by
  have key : ∀ c : Fin m → ℤ, NG.infOf c =
      (Finset.univ.val.map fun i : Fin m => c i - (i : ℕ)).map fun z : ℤ => (z : ℂ) + ((m : ℂ) - 1) / 2 := fun c => by
    rw [NG.infOf, Multiset.map_map]
    congr 1
    funext i
    simp only [Function.comp]
    push_cast
    ring
  rw [key, key] at h
  have h2 := Multiset.map_injective (fun x y hxy => by exact_mod_cast add_right_cancel hxy) h
  have sa : ∀ c : Fin m → ℤ, Antitone c → StrictAnti fun i : Fin m => c i - (i : ℕ) := fun c hc i j hij => by
    have := hc hij.le
    have h3 : (i : ℕ) < j := hij
    beta_reduce
    omega
  have hr : Set.range (fun i : Fin m => a i - (i : ℕ)) = Set.range fun i : Fin m => b i - (i : ℕ) := by
    ext z
    have := congrArg (z ∈ ·) h2
    simpa using this
  have h4 := ((sa a ha).range_inj (sa b hb)).1 hr
  funext i
  have := congrFun h4 i
  omega

end GlobalTheory.MtRead
end
