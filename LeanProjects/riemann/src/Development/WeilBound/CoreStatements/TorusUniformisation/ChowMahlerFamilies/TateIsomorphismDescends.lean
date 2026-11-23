import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TateIsomorphismDescent

theorem exists_weilIs (S : Scheme.{0}) (P : Out.PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (hx : x ^ k = 1)
    (hy : y ^ k = 1) : ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L k x y c :=
  (GlobalTheory.CommutatorPairing.existsUnique_weilIs GlobalTheory.abelianSchemeLaws_all.1.globalFns
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
    S P k T x y hx hy).exists

theorem exists_root {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) {n : ℕ} (hn : 0 < n) (z : Ωˣ)
    (hz : z ^ n = 1) : ∃ w : Kˣ, Units.map i.toMonoidHom w = z := by
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).Splits := IsAlgClosed.splits _
  have hne : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn 1
  have hm : (z : Ω) ∈ ((Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).map i).roots := by
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne)]
    simp [hz']
  rw [hs.roots_map_of_injective i.injective] at hm
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hm
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact z.ne_zero (hw.symm.trans (map_zero i))
  exact ⟨Units.mk0 w hw0, Units.ext hw⟩

end PositivityTheory.Xgn.TateIsomorphismDescent

theorem PositivityTheory.Xgn.tate_isomorphism_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)), (∀ c, IsMonHom (act c)) → ∀ (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (u : Over.mk x' ⟶ Over.mk x), u.left = spMap i → ∀ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n v, 0 < n → I'.ev n v = u ≫ I.ev n v := by
  intro E _ _ _ H D S P act hact K Ω _ _ _ _ _ i x x' u hu I'
  have laws := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero Ω := (RingHom.charZero_iff i.injective).1 ‹_›
  let f : (Over.mk x ⟶ P.A) →* (Over.mk x' ⟶ P.A) := MonoidHom.mk' (u ≫ ·) (MonObj.comp_mul u)
  have hinj : Function.Injective f := GlobalTheory.TorsionFieldExt.comp_injective u P.A
  have ginj : Function.Injective (Units.map i.toMonoidHom : Kˣ →* Ωˣ) := Units.map_injective i.injective
  have hu' : ∀ c : Kˣ, unitOn (Units.map i.toMonoidHom c) = Units.map u.left.appTop.hom.toMonoidHom (unitOn c) :=
    fun c => by
      rw [hu]
      exact Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)))
  have hev : ∀ (n : ℕ) (v : D.La), ∃ y : Over.mk x ⟶ P.A, (n = 0 → y = 1) ∧ (0 < n → f y = I'.ev n v) := by
    intro n v
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun _ => rfl, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨y, -, hy⟩ := GlobalTheory.TorsionFieldExt.exists_of_isAlgClosed laws P u (Nat.cast_ne_zero.2 hn.ne')
        (Nat.cast_ne_zero.2 hn.ne') (I'.ev n v) ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun h => absurd h hn.ne', fun _ => hy⟩
  choose ev ev0 evp using hev
  have hζ : ∀ n : ℕ, ∃ w : Kˣ, 0 < n → Units.map i.toMonoidHom w = I'.ζ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨w, hw⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_root i hn (I'.ζ n) (I'.ζ_prim n hn).pow_eq_one
      exact ⟨w, fun _ => hw⟩
  choose ζ hζ using hζ
  have tors : ∀ n, 0 < n → ∀ a, ev n a ^ n = 1 := fun n hn a => hinj (by
    rw [map_pow, evp n a hn, map_one]; exact (I'.onto n hn _).2 ⟨a, rfl⟩)
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => IsPrimitiveRoot.of_map_of_injective (f := (Units.map i.toMonoidHom : Kˣ →* Ωˣ))
              (by rw [hζ n hn]; exact I'.ζ_prim n hn) ginj
            ζ_pow := fun n m hn hm => ginj (by
              rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm])
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← evp n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => hinj (by
              rw [map_pow, evp _ a (Nat.mul_pos hn hm), evp n a hn, I'.tower n m hn hm])
            isom := fun n hn a b => ?_ }, fun n v hn => (evp n v hn).symm⟩
  · rcases Nat.eq_zero_or_pos n with h | hn
    · rw [ev0 n _ h, ev0 n _ h, ev0 n _ h, _root_.mul_one]
    · exact hinj (by rw [map_mul, evp n _ hn, evp n _ hn, evp n _ hn, I'.add])
  · rcases Nat.eq_zero_or_pos n with h | hn
    · have := hact c
      rw [ev0 n _ h, ev0 n _ h]
      exact (MonObj.one_comp (act c)).symm
    · refine hinj ?_
      rw [evp n _ hn, I'.lin, ← evp n a hn]
      exact Category.assoc u (ev n a) (act c)
  · obtain ⟨a, ha⟩ := (I'.onto n hn (f z)).1 (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj ((evp n a hn).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact tors n hn a
  · obtain ⟨c, hc⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_weilIs S P n _ _ _ (tors n hn a) (tors n hn b)
    obtain ⟨w, rfl⟩ : ∃ w : Kˣ, unitOn w = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val)⟩
    have h₁ := GlobalTheory.CommPairing.weilIs_pull laws.globalFns P.isAb P.isLB u hc
    rw [← hu'] at h₁
    have h₂ := I'.isom n hn a b
    rw [← evp n a hn, ← evp n b hn, ← hζ n hn, ← map_zpow] at h₂
    have e := ginj (GlobalTheory.weilIs_unique_fieldPoint S P.A P.L P.isLB Ω x' n _ _ _ _ h₁ h₂)
    rw [← e]
    exact hc
