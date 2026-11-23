import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiAffineSubgroupContainingTorusEqTorusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.PowLocus
open GlobalTheory.AbLaw

theorem card_torsion_le {Γ T J : Type} [Group Γ] [Group T] [Finite J] (hΓ : ∀ a b : Γ, Commute a b)
    (i : T →* Γ) (hi : Function.Injective i) (P : Γ → Prop) (c : {x // P x} → J)
    (hc : ∀ x y, c x = c y → ∃ t, i t = x.1 * y.1⁻¹) (n : ℕ) [Finite {t : T // t ^ n = 1}] :
    Finite {x : Γ // P x ∧ x ^ n = 1} ∧
      Nat.card {x : Γ // P x ∧ x ^ n = 1} ≤ Nat.card J * Nat.card {t : T // t ^ n = 1} := by
  rcases isEmpty_or_nonempty {x : Γ // P x ∧ x ^ n = 1} with h | h
  · exact ⟨inferInstance, by simp⟩
  let d : {x : Γ // P x ∧ x ^ n = 1} → J := fun x => c ⟨x.1, x.2.1⟩
  have h1 : ∀ x : {x : Γ // P x ∧ x ^ n = 1}, ∃ t : {t : T // t ^ n = 1},
      i t.1 = x.1 * (Function.invFun d (d x)).1⁻¹ := by
    intro x
    have e : d (Function.invFun d (d x)) = d x := Function.invFun_eq ⟨x, rfl⟩
    obtain ⟨t, ht⟩ := hc _ _ e.symm
    refine ⟨⟨t, hi ?_⟩, ht⟩
    rw [map_pow, ht, map_one, (hΓ _ _).mul_pow, inv_pow]
    change x.1 ^ n * ((Function.invFun d (d x)).1 ^ n)⁻¹ = 1
    rw [x.2.2, (Function.invFun d (d x)).2.2, inv_one, _root_.mul_one]
  choose τ hτ using h1
  have hinj : Function.Injective fun x => (d x, τ x) := by
    intro x y hxy
    have e1 : d x = d y := congrArg Prod.fst hxy
    have e2 : τ x = τ y := congrArg Prod.snd hxy
    have e3 := hτ x
    rw [e1, e2, hτ y] at e3
    exact Subtype.ext (mul_right_cancel e3).symm
  exact ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans (Nat.card_prod _ _).le⟩

theorem torus_torsion (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (n : ℕ) (hn : 1 ≤ n) :
    Finite {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X // t ^ n = 1} ∧
      Nat.card {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X // t ^ n = 1} ≤ n ^ Module.finrank ℤ X := by
  haveI : NeZero n := ⟨by omega⟩
  let b := Module.finBasis ℤ X
  let e₁ := splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))
  let e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ ≃* kˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  let f : {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X // t ^ n = 1} →
      (Fin (Module.finrank ℤ X) → rootsOfUnity n k) := fun t j =>
    ⟨e₃ (e₁ t.1 (Multiplicative.ofAdd (b j))), by
      rw [mem_rootsOfUnity, ← map_pow, ← MonoidHom.pow_apply, ← map_pow, t.2, map_one,
        MonoidHom.one_apply, map_one]⟩
  have hf : Function.Injective f := by
    intro s t h
    refine Subtype.ext (e₁.injective ?_)
    have : (MonoidHom.toAdditiveRight (e₁ s.1)).toIntLinearMap =
        (MonoidHom.toAdditiveRight (e₁ t.1)).toIntLinearMap :=
      b.ext fun j => congrArg Additive.ofMul (e₃.injective (congrArg Subtype.val (congrFun h j)))
    refine MonoidHom.ext fun x => ?_
    exact congrArg Additive.toMul (DFunLike.congr_fun this x)
  refine ⟨Finite.of_injective _ hf, (Nat.card_le_card_of_injective _ hf).trans ?_⟩
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
  exact Nat.pow_le_pow_left (by simpa using card_rootsOfUnity k n) _

theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  have h2 : ν.left.ker ≤ g.left.ker := by
    refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g.left ν.left.ker.support ?_)
    · rw [Scheme.IdealSheafData.vanishingIdeal_support]
      exact Scheme.IdealSheafData.le_radical _
    · rw [Scheme.Hom.support_ker]
      exact h.trans subset_closure
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem exists_basicOpen_eq {Y : Scheme.{0}} {M : LB Y} (hM : M.IsLB) (m n : ℕ) (hm : 0 < m)
    (t : ∀ i, Γ(Y, M.U i)ˣ) (e2 : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ _) (t i) =
      M.g i j ^ (m : ℤ) * res inf_le_right (t j))
    (s : ∀ i, Γ(Y, M.U i)) (e1 : ∀ i j, rs Y (inf_le_left : M.U i ⊓ M.U j ≤ _) (s i) =
      (M.g i j ^ (n : ℤ)).val * rs Y inf_le_right (s j)) :
    ∃ f : Γ(Y, ⊤), Y.basicOpen f = ⨆ i, Y.basicOpen (s i) := by
  obtain ⟨f, hf, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun _ => homOfLE le_top) hM.cover.ge
    (fun i => (s i ^ m * ((t i)⁻¹ ^ n).val : Γ(Y, M.U i))) (by
    intro i j
    change rs Y (inf_le_left : M.U i ⊓ M.U j ≤ _) (s i ^ m * ((t i)⁻¹ ^ n).val) =
      rs Y inf_le_right (s j ^ m * ((t j)⁻¹ ^ n).val)
    have e3 : ∀ {V W : Y.Opens} (h : W ≤ V) (u : Γ(Y, V)ˣ), rs Y h u.val = (res h u).val :=
      fun _ _ => rfl
    rw [map_mul, map_mul, e3, e3, map_pow, map_pow, map_pow, map_pow, map_inv, map_inv, e1, e2]
    rw [zpow_natCast, zpow_natCast, mul_pow, ← Units.val_pow_eq_pow_val, mul_right_comm, ← Units.val_mul,
      mul_comm _ (_ ^ m)]
    congr 2
    rw [mul_inv, mul_pow, ← _root_.mul_assoc, inv_pow, ← pow_mul, ← pow_mul, mul_comm n m,
      mul_inv_cancel, _root_.one_mul])
  refine ⟨f, ?_⟩
  have key : ∀ i, M.U i ⊓ Y.basicOpen f = Y.basicOpen (s i) := by
    intro i
    have h1 := Y.basicOpen_res f (homOfLE (le_top : M.U i ≤ ⊤)).op
    rw [← h1]
    refine (congrArg Y.basicOpen (hf i)).trans ?_
    beta_reduce
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ hm, Y.basicOpen_of_isUnit (Units.isUnit _)]
    exact inf_eq_left.2 (Y.basicOpen_le _)
  simp only [← key]
  rw [← iSup_inf_eq, hM.cover, top_inf_eq]

theorem exists_finite_classes {k : Type} [Field k] {N₀ N : Over (Sp k)} [GrpObj N₀] [GrpObj N]
    [TopologicalSpace.NoetherianSpace N.left] (μ₀ : N₀ ⟶ N) [IsMonHom μ₀] [IsOpenImmersion μ₀.left]
    [IsClosedImmersion μ₀.left] :
    ∃ (J : Type) (_ : Finite J) (c : (𝟙_ (Over (Sp k)) ⟶ N) → J),
      ∀ x y, c x = c y → ∃ z : 𝟙_ (Over (Sp k)) ⟶ N₀, z ≫ μ₀ = x * y⁻¹ := by
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have hsub : Subsingleton (𝟙_ (Over (Sp k))).left := inferInstanceAs (Subsingleton (Sp k))
  refine ⟨irreducibleComponents N.left, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents,
    fun x => ⟨irreducibleComponent (x.left pt), irreducibleComponent_mem_irreducibleComponents _⟩,
    fun x y h => exists_lift μ₀ _ ?_⟩
  have h' : irreducibleComponent (x.left pt) = irreducibleComponent (y.left pt) := congrArg Subtype.val h
  let τ : N ⟶ N := 𝟙 N * (toUnit N ≫ y⁻¹)
  have hτ : ∀ w : 𝟙_ (Over (Sp k)) ⟶ N, w ≫ τ = w * y⁻¹ := fun w => by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (w ≫ toUnit N) (𝟙 _),
      Category.id_comp]
  have hcl : IsClopen (Set.range μ₀.left) :=
    ⟨μ₀.left.isClosedEmbedding.isClosed_range, μ₀.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (τ.left '' irreducibleComponent (x.left pt)) :=
    (isIrreducible_irreducibleComponent.isConnected.isPreconnected).image _
      τ.left.continuous.continuousOn
  have hs := hpre.subset_isClopen hcl ⟨τ.left (y.left pt), ⟨_, h' ▸ mem_irreducibleComponent, rfl⟩,
    ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N₀).left pt, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hτ,
        mul_inv_cancel, MonObj.one_comp]⟩⟩
  rintro _ ⟨p, rfl⟩
  rw [hsub.elim p pt, ← hτ, Over.comp_left, Scheme.Hom.comp_apply]
  exact hs ⟨_, mem_irreducibleComponent, rfl⟩

theorem exists_basicOpen_eq_of_pullPow {Y Z : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (ν : Z ⟶ Y)
    {F P : Y ⟶ Y} {a b : ℤ} (hab : a < b) (h₁ : PullPow F L a) (h₂ : PullPow P L b)
    (h : ν ≫ F = ν ≫ P) (n : ℕ) (s : LB.Sec (pw (L.pull ν) n)) :
    ∃ f : Γ(Z, ⊤), Z.basicOpen f = Out.nonzeroLocus s := by
  have h₁' : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 _] ![1, -a] := h₁
  have h₂' : MulPull.HasGen L (K := Fin 2) ![P, 𝟙 _] ![1, -b] := h₂
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_pos.2 hab).le
  have hm0 : 0 < m := by omega
  obtain ⟨t, ht⟩ : MulPull.HasGen L (K := PUnit) (fun _ => ν) (fun _ => (m : ℤ)) :=
    ((h₁'.pull ν).mul (h₂'.pull ν).inv).of_formEq hL fun U _ u => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, Fintype.prod_unique, ← hm]
      change u (ν ≫ F) ^ (1 : ℤ) * u (ν ≫ 𝟙 _) ^ (-a) * (u (ν ≫ P) ^ (-1 : ℤ) * u (ν ≫ 𝟙 _) ^ (- -b)) = _
      rw [h, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  refine exists_basicOpen_eq (pull_isLB hL ν) m n hm0 t.s (fun i j => (ht i j).trans ?_) s.f s.compat
  refine congrArg₂ (· * ·) ?_ rfl
  have key : ∀ (U : Type) [CommGroup U] (g : PUnit.{1} → U),
      ∏ k, g k ^ (m : ℤ) = (∏ k, g k ^ (1 : ℤ)) ^ (m : ℤ) := fun U _ g => by simp
  exact key _ fun k => res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit.{1} => ν) i k))
    (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit.{1} => ν) j k)) :
      LB.wchart L (fun _ : PUnit.{1} => ν) i ⊓ LB.wchart L (fun _ : PUnit.{1} => ν) j ≤
        ν ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k))) (pullU ν _ (L.g (i k) (j k)))

theorem card_torsion_powLocus_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : G ⟶ G) (Q : ℕ), 2 ≤ Q → IsMonHom F → PullPow F.left L Q → i ≫ F = i ^ Q → ∃ C : ℕ, ∀ n, 1 ≤ n → Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X := by
  intro k _ _ G _ hG X _ _ _ B _ i q hq hB L hL F Q hQ hF hP hi
  obtain ⟨hc, hsm, hsep, hqc, hgc⟩ := id hG
  obtain ⟨hi₁, -, -, -, -, hpb, -⟩ := id hq
  have hcomm : ∀ a b : 𝟙_ (Over (Sp k)) ⟶ G, Commute a b := fun a b => mul_comm a b
  have hred₁ : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))

  let e := equalizer.ι F ((𝟙 G) ^ Q)
  have he : IsClosedImmersion e.left := isClosedImmersion_equalizer_ι_left _ _
  have hpw : ∀ {T : Over (Sp k)} (x : T ⟶ G), x ≫ (𝟙 G) ^ Q = x ^ Q := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  have hin : ∀ {T : Over (Sp k)} (x : T ⟶ G), x ≫ F = x ^ Q → Set.range x.left ⊆ Set.range e.left := by
    intro T x hx
    rw [← equalizer.lift_ι (f := F) (g := (𝟙 G) ^ Q) x (hx.trans (hpw x).symm), Over.comp_left]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ p).symm⟩
  have hout : ∀ {T : Over (Sp k)} [IsReduced T.left] (x : T ⟶ G),
      Set.range x.left ⊆ Set.range e.left → x ≫ F = x ^ Q := by
    intro T _ x hx
    obtain ⟨l, rfl⟩ := exists_lift e x hx
    refine Eq.trans ?_ (hpw _)
    rw [Category.assoc, Category.assoc, equalizer.condition]
  let C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | x ≫ F = x ^ Q}
      one_mem' := (MonObj.one_comp F).trans (one_pow Q).symm
      mul_mem' := fun {a b} ha hb => (MonObj.mul_comp a b F).trans
        ((congrArg₂ (· * ·) ha hb).trans ((hcomm a b).mul_pow Q).symm)
      inv_mem' := fun {a} ha => (GrpObj.inv_comp a F).trans
        ((congrArg (·⁻¹) ha).trans (inv_pow a Q).symm) }
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance C
    (Set.range e.left) e.left.isClosedEmbedding.isClosed_range fun x => ⟨hin x, hout x⟩
  have hNq : QuasiCompact N.hom := by rw [← Over.w ν]; infer_instance
  obtain ⟨N₀, _, μ₀, g, hμ, hμo, hμc, hgc₀, hsm₀, -⟩ := exists_neutralComponent k N hNs hNq
  have : Mono ν := Over.mono_of_mono_left ν
  have : Mono μ₀ := Over.mono_of_mono_left μ₀
  have hs₀ : Smooth N₀.hom := SmoothOfRelativeDimension.smooth g _
  have hN₀ : SmConn N₀ := by
    refine ⟨⟨?_⟩, hs₀, ?_, ?_, hgc₀⟩
    · rw [← cancel_mono (μ₀ ≫ ν), Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← BraidedCategory.braiding_naturality, Category.assoc, IsCommMonObj.mul_comm]
    · rw [← Over.w (μ₀ ≫ ν), Over.comp_left]; infer_instance
    · rw [← Over.w (μ₀ ≫ ν), Over.comp_left]; infer_instance
  have hcl₀ : IsClosedImmersion (μ₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance

  obtain ⟨-, -, -, -, -, -, hTi, -⟩ := (splitTorus_properties (Sp k)).1 X
  have hT : IsIntegral (splitTorus (Sp k) X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (splitTorus (Sp k) X).hom
  obtain ⟨i₁, hi₁'⟩ := exists_lift ν i (hr ▸ hin i hi)
  have hone : (1 : 𝟙_ (Over (Sp k)) ⟶ _) ≫ i₁ = (1 : 𝟙_ (Over (Sp k)) ⟶ _) ≫ μ₀ := by
    rw [← cancel_mono ν, Category.assoc, hi₁', MonObj.one_comp, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨i', hi'⟩ := exists_lift μ₀ i₁ ((isPreconnected_range i₁.left.continuous).subset_isClopen
    ⟨μ₀.left.isClosedEmbedding.isClosed_range, μ₀.left.isOpenEmbedding.isOpen_range⟩
    ⟨((1 : 𝟙_ (Over (Sp k)) ⟶ _) ≫ i₁).left (IsLocalRing.closedPoint k),
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩, by
        rw [hone]; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩⟩)

  have hNl : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hNr : IsReduced N₀.left := GlobalTheory.isReduced_of_smooth_of_isReduced N₀.hom
  have hF₀ : (μ₀ ≫ ν).left ≫ F.left = (μ₀ ≫ ν).left ≫ ((𝟙 G) ^ Q).left := by
    rw [← Over.comp_left, ← Over.comp_left, hpw]
    refine congrArg _ (hout _ ?_)
    rw [← hr, Over.comp_left]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ p).symm⟩
  obtain ⟨hA, hB'⟩ := AmpSub.ampleCub_pull_and_pullPow (Sp k) G L hL
  obtain ⟨-, -, -, n, -, hamp⟩ := hA N₀ (μ₀ ≫ ν) inferInstance hcl₀
  have h₂ := hB' ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.isLocalRing)
    inferInstance Q
  have hqa : ∀ x : N₀.left, ∃ f : Γ(N₀.left, ⊤), x ∈ N₀.left.basicOpen f ∧
      IsAffineOpen (N₀.left.basicOpen f) := by
    intro x
    obtain ⟨s, hx, hs⟩ := hamp x
    obtain ⟨f, hf⟩ := exists_basicOpen_eq_of_pullPow hL.1 (μ₀ ≫ ν).left
      (by have : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
          nlinarith) hP h₂ hF₀ n s
    exact ⟨f, hf ▸ hx, hf ▸ hs⟩
  have hK := GlobalTheory.T.quasiAffine_subgroup_containing_torus_eq_torus k G hG X B i q hq hB N₀ (μ₀ ≫ ν) i' hN₀ inferInstance hcl₀
    (by rw [← Category.assoc, hi', hi₁']) hqa

  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  obtain ⟨J, _, c, hc'⟩ := exists_finite_classes μ₀
  have hl : ∀ x : {x : 𝟙_ (Over (Sp k)) ⟶ G // x ≫ F = x ^ Q}, ∃ l, l ≫ ν = x.1 :=
    fun x => exists_lift ν x.1 (hr ▸ hin x.1 x.2)
  choose l hl using hl
  have : Mono i := ⟨fun a b h => hpb.hom_ext h (toUnit_unique _ _)⟩
  refine ⟨Nat.card J, fun r hr1 => ?_⟩
  obtain ⟨hfin, hle⟩ := torus_torsion k X r hr1
  obtain ⟨h3, h4⟩ := card_torsion_le hcomm
    (MonoidHom.mk' (fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X => t ≫ i) fun a b => MonObj.mul_comp a b i)
    (fun a b h => (cancel_mono i).1 h) (fun x => x ≫ F = x ^ Q) (fun x => c (l x)) (fun x y h => by
      obtain ⟨z, hz⟩ := hc' _ _ h
      obtain ⟨t, ht⟩ := hK z
      refine ⟨t, ht.trans ?_⟩
      rw [← Category.assoc, hz, MonObj.mul_comp, GrpObj.inv_comp, hl, hl]) r
  exact ⟨h3, h4.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.SS.PowLocus
end
