import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePowerStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpTotal
open GlobalTheory.TwistLoc (gc gc_mul)

section General
variable {X X' W Y Z : Scheme.{0}}

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (scal p a) = gc (r ≫ p) z a := gs_pull r p z ⊤ trivial _

theorem gc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a : R) :
    gc (q ≫ Spec.map (CommRingCat.ofHom f)) z a = gc q z (f a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_comb {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (c : Fin n → Γ(Y, ⊤))
    (t : Fin n → LB.Sec (LB.LinComb L φ ε)) : ∃ s : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = ∑ i, gs r z ⊤ (c i) * sval (t i) r z J :=
  ⟨⟨fun j => ∑ i, (IndivisibleSection.smulSec (c i) (t i)).f j, fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (IndivisibleSection.smulSec (c l) (t l)).compat i j⟩,
    fun Z r z J hJ => DVR.SectionScalarValuation.sval_lin c t (fun _ => rfl) r z hJ⟩

theorem exists_inv {L : LB X} {L' : LB X'} {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) : ∃ v : LB.Iso (L.pull F) (L'.pull F'), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
        gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := by
  let v : LB.Iso (L.pull F) (L'.pull F') := ⟨fun p => (res (le_inf inf_le_right inf_le_left :
    (L'.pull F').U p.1 ⊓ (L.pull F).U p.2 ≤ (L.pull F).U p.2 ⊓ (L'.pull F').U p.1) (w.s (p.2, p.1)))⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
      gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := fun Z r z i j hi hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _
      (show r z ∈ (L'.pull F').U (fun _ => j) ⊓ (L.pull F).U (fun _ => i) from ⟨mem_pull.2 hj, mem_pull.2 hi⟩) _))
  refine ⟨v, (isGen_iff v).2 fun Z r z j j' i i' hj hj' hi hi' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z r z (i PUnit.unit) (i' PUnit.unit) (fun _ => j) (fun _ => j') (mem_pull.1 hi)
    (mem_pull.1 hi') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [gm_pull_g L' F' r z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
  refine (hv Z r z (i PUnit.unit) j (mem_pull.1 hi) hj).trans ?_
  rw [e, gm_pull_g L F r z i i' hi hi']
  refine Eq.trans ?_ (congrArg _ (hv Z r z (i' PUnit.unit) j' (mem_pull.1 hi') hj')).symm
  rw [mul_inv, mul_inv, inv_inv, mul_comm _⁻¹]

end General

theorem exists_span (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (s : LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => (snd (Over.mk q) P.A).left) (fun _ => (n : ℤ)))) :
    ∃ (m : ℕ) (c : Fin m → F) (a : Fin m → LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => (n : ℤ)))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk q ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = ∑ i, gc (R := F) (r ≫ (fst (Over.mk q) P.A).left) z (c i) *
          sval (a i) (r ≫ (snd (Over.mk q) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have hi : (Spec (CommRingCat.of K)).topIso.inv ≫
      (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = 𝟙 _ :=
    (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom ≫ (Spec (CommRingCat.of K)).topIso.inv
      = 𝟙 _ :=
    (congrArg (· ≫ _) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.hom_inv_id
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).left,
      t ≫ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = q :=
    ⟨q ≫ (Spec (CommRingCat.of K)).topIso.inv, (Category.assoc _ _ _).trans
      ((congrArg (q ≫ ·) hi).trans (Category.comp_id q))⟩
  let T₀ := overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤
  let e : P.A ⟶ T₀ ⊗ P.A := lift (Over.homMk (P.A.hom ≫ (Spec (CommRingCat.of K)).topIso.inv)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hi).trans (Category.comp_id _)))) (𝟙 _)
  have he : snd (baseAt t) P.A ≫ e = homAt t ▷ P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext ?_) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((Category.comp_id _).trans (whiskerRight_snd (homAt t) P.A).symm)))
    have : IsIso T₀.hom := ⟨_, hi', hi⟩
    rw [← cancel_mono T₀.hom, Over.w, Over.w]
  choose a ha using fun i => PullSec.exists_pullSec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) e.left
    (fun _ => (congrArg CommaMorphism.left (lift_snd _ _ : e ≫ snd _ _ = _)).symm) (b i)
  choose b' hb' using fun i => IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  have hsp := (hb F t b' fun i j => hb' i j _).2
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (d i)
  refine ⟨_, c, a, fun Z r z J hJ => ?_⟩
  refine (DVR.SectionScalarValuation.sval_lin (s := s) (fun i => scal (R := F) (fst (baseAt t) P.A).left (c i)) b' (fun j => ?_) r z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (gs_scal _ r z _) ?_)
  · refine (congrFun (congrArg Subtype.val hd) j).symm.trans ?_
    refine (congrFun (Submodule.coe_sum _ _ _) j).trans ((Finset.sum_apply _ _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_))
    rw [← hc i]
    rfl
  · have e₁ : (r ≫ (snd (baseAt t) P.A).left) ≫ e.left = r ≫ (homAt t ▷ P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left he))
    have e₂ : (r ≫ (homAt t ▷ P.A).left) ≫ (snd T₀ P.A).left = r ≫ (snd (baseAt t) P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)))
    refine Eq.trans ?_ (ha i Z _ z J hJ).symm
    rw [e₁, sval_of (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (b i) _ z J
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left)) (fun _ => congrArg J e₂)]
    have hm := hJ.mem (fun _ : Fin 1 => (snd (baseAt t) P.A).left) r
    have le := chart_le_res P.A P.L (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) n
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left))
    exact (congrArg (gs r z _) (hb' i _ le)).trans ((gs_res r z le hm _).trans (gs_pull r (homAt t ▷ P.A).left z _ (le hm) _))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : PreU I D A G) (k : ℕ)
    (a : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (k : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ ∃ σ : U.SecGT (𝟙_ _) k, ∀ (Z : Scheme.{0}) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        sval σ rG z JG = gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z t *
          ((gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval a (y ≫ U.gen.hom.left) z JA) := by
  have := U.semi.quasiCompact
  have := U.semi.separated
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨v, hv, hvw⟩ := exists_inv U.wA U.wA_gen
  obtain ⟨s', hs'⟩ := PullSec.exists_sec_of_iso A.isLB U.P.L.isLB v hv (𝟙 _) U.gen.hom.left
    (pullback.fst G.hom (jK R) ≫ 𝟙 G.left) (𝟙 A.A.left) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) k a
  obtain ⟨t, ht, σ₀, hσ₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) U.P.L.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) s'
  obtain ⟨σ, hσ⟩ := PullSec.exists_pullSec U.P.L.isLB (φ' := fun _ : Fin 1 => (snd (𝟙_ _) G).left)
    (snd (𝟙_ _) G).left (fun _ => (Category.comp_id _).symm) σ₀
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun Z y rG e z JA JG hA hG => (hσ Z rG z JG hG).trans ?_⟩
  have mA := hA (y ≫ U.gen.hom.left)
  have mG := hG (y ≫ pullback.fst G.hom (jK R))
  rw [e, sval_of σ₀ _ z JG (fun _ => JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG (Category.comp_id _)),
    sval_of a _ z JA (fun _ => JA (y ≫ U.gen.hom.left)) (fun _ => congrArg JA (Category.comp_id _))]
  refine (hσ₀ Z y z _ (Set.mem_iInter.2 fun _ => mG)).trans (congrArg _ ?_)
  have h := hs' Z y z _ _ mA mG
  rw [Category.comp_id y, hvw Z y z _ _ mG mA] at h
  refine Eq.trans ?_ (congrArg _ h)
  rw [← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, _root_.one_mul]

theorem exists_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X)
    (f : SecBT D (𝟙_ _) k α) : ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
        rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
          sval s rF z J = sval f rB z J := by
  let φ := toUnit (TF (R := R) F)
  have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd (𝟙_ _) D.P.A := (whiskerRight_snd _ _).symm
  have hc : ∀ i : Fin 4, DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D (𝟙_ _) α i := fun i => by
    have u : φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  obtain ⟨s, hs⟩ := PullSec.exists_pullSec D.P.isLB (φ ▷ D.P.A).left hc f
  refine ⟨s, fun Z rF rB e z J hJ => (hs Z rF z J hJ).trans (congrArg (sval f · z J) ?_)⟩
  have : IsIso (snd (𝟙_ _) D.P.A) := by rw [← leftUnitor_hom]; infer_instance
  have : IsIso (snd (𝟙_ _) D.P.A).left := inferInstanceAs (IsIso ((Over.forget _).map (snd (𝟙_ _) D.P.A)))
  rw [← cancel_mono (snd (𝟙_ _) D.P.A).left, e]
  exact (Category.assoc _ _ _).trans (congrArg (rF ≫ ·) (congrArg CommaMorphism.left a₀).symm)

theorem exists_expF (hS : SecBaseChangeSt) (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : 1 ≤ k) (hb : ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s, U.ExpF F k t s := by
  obtain ⟨n, c, a, ha⟩ := exists_span hS A k hk F (jFK (R := R) F) t
  choose d hd σ hσ using fun i => exists_integral U k (a i)
  choose f hf using fun i => hb (σ i)
  choose g hg using fun i α => exists_pullB D F k α (f i α)
  let ψ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hψ : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero (algebraMap (FractionRing R) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  choose s hs using fun α => exists_comb
    (fun i => scal (R := F) (fst (TF (R := R) F) D.P.A).left (c i * (ψ (d i))⁻¹)) (fun i => g i α)
  refine ⟨s, n, fun i => c i * (ψ (d i))⁻¹, σ, f, hf, fun Z rA y rG e₁ e₂ z JA JG hA hG => ?_,
    fun α Z rF rB e z J hJ => (hs α Z rF z J hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg i α Z rF rB e z J hJ))⟩
  refine (congrArg _ (ha Z rA z JA hA)).trans ((Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom =
      ((rA ≫ (fst (TFK (R := R) F) A.A).left) ≫ jFK (R := R) F) ≫ jK R := by
    have w₁ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    have w₂ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (congrArg (y ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) ?_))
    exact (congrArg (y ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.A.hom) e₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))
  have e₄ : gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i) =
      gc (R := F) (rA ≫ (fst (TFK (R := R) F) A.A).left) z (ψ (d i)) :=
    (congrArg (gc · z (d i)) e₃).trans ((gc_map _ _ z _).trans (gc_map _ _ z _))
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_scal (R := F) _ rA z _) (hσ i Z y rG e₂ z JA JG hA hG)).symm
  rw [e₄, ← _root_.mul_assoc (gc _ _ _) (gc _ _ _), ← gc_mul, inv_mul_cancel_right₀ (hψ i)]
  exact (mul_left_comm _ _ _).trans (congrArg (fun q => _ * (_ * sval (a i) q z JA)) e₁)

theorem expF_total : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) :=
  fun h h₂ V _ _ _ hV D A G _ _ U F _ _ k hk t =>
    exists_expF h.secBaseChange U F k hk (GlobalTheory.T.exists_expansion_section_lineBundle_power h h₂ V hV D A G U k hk) t

end GlobalTheory.UU.ExpTotal
end
