import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympRep

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def PtC {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type) [Field k]
    (y : Sp k ⟶ S) (z : kˣ) (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)) : Prop :=
  (∀ a, f a = 1 ↔ ∃ c, a = M • c) ∧ (∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, f a = g) ∧
    ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (f a) (f c) (unitOn (z ^ (2 * omegaStd a c)))

theorem ptC_congr {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type)
    [Field k] (z : kˣ) {y y' : Sp k ⟶ S} (hy : y = y') (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A))
    (f' : (Fin h ⊕ Fin h → ℤ) → (Over.mk y' ⟶ o.A)) (hf : ∀ a, (f a).left = (f' a).left) :
    PtC o h M k y z f ↔ PtC o h M k y' z f' := by
  subst hy
  obtain rfl : f = f' := funext fun a => Over.OverMorphism.ext (hf a)
  rfl

theorem lemCyc : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover

theorem lemKer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric

theorem lemOnto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint

theorem lemWeil : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := GlobalTheory.T.weilPairing_condition_locus_isClopen

theorem exists_sympLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  intro p _ D R _ b N h M hM hcop S t o
  have hM0 : M ≠ 0 := hM.ne'
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (b.unit M hcop).map (GlobalTheory.LevCover.fnOn t)
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, eadd, epow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A M (Fin h ⊕ Fin h → ℤ) o.ab hMS
  haveI := hfin
  haveI := het
  obtain ⟨S', t₀, hS1, hS2, hSu⟩ := lemCyc M S hM hMS
  haveI := hS1
  haveI := hS2
  obtain ⟨hW1, hW2⟩ := GlobalTheory.LevCover.finiteEtale_tensor Z S'
  haveI := hW1
  haveI := hW2
  let W : Over S := Z ⊗ S'
  let e : (Fin h ⊕ Fin h → ℤ) → (W ⟶ o.A) := fun a => fst Z S' ≫ et a
  let τ : W.left ⟶ Sp (cycAway M) := (snd Z S').left ≫ t₀
  have eadd' : ∀ a c, e (a + c) = e a * e c := fun a c => by simp only [e, eadd, MonObj.comp_mul]
  have epow' : ∀ a, e a ^ M = 1 := fun a => by simp only [e]; rw [← MonObj.comp_pow, epow, MonObj.comp_one]
  let C : Prop := M = 1 ∨ 2 * h = Module.finrank ℤ D.La
  obtain ⟨Vs, hVs, HV⟩ := (lemKer S o.A o.ab M h hM hMS W e eadd' epow').and
    ((GlobalTheory.HkClopen.Loc.const (S := W.left) C).and (lemWeil p D R b N h M hM hcop S t o W τ e eadd' epow'))
  let U : W.left.Opens := ⟨Vs, hVs.isOpen⟩
  obtain ⟨Y, i, hY1, hY2, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub U hVs.isClosed
  have memIff : ∀ (T : Over S) (w : T ⟶ W) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left)
      (β : cycAway M →+* k) (z : kˣ), (x ≫ w.left) ≫ τ = spMap β → (z : k) = β (zetaAway M) →
      ((x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs ↔
        PtC o h M k (x ≫ T.hom) z (fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ w ≫ e a)) := by
    intro T w k _ _ x β z hβ hz
    rw [HV k (x ≫ w.left), ← ptC_congr o h M k z (show (x ≫ w.left) ≫ W.hom = x ≫ T.hom by
      rw [Category.assoc, Over.w w]) (fun a => (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a)
      _ (fun a => by simp)]
    have ha : ∀ a c, (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e (a + c) =
        ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) *
          ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e c) := fun a c => by
      rw [eadd', MonObj.comp_mul]
    have hp : ∀ a, ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) ^ M = 1 :=
      fun a => by rw [← MonObj.comp_pow, epow', MonObj.comp_one]
    constructor
    · rintro ⟨hk, hC, hw⟩
      exact ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).2 hC, hw β z hβ hz⟩
    · rintro ⟨hk, ho, hw⟩
      refine ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).1 ho, fun β' z' hβ' hz' => ?_⟩
      obtain rfl : β' = β := GlobalTheory.LevCover.spMap_inj' (hβ'.symm.trans hβ)
      obtain rfl : z' = z := Units.ext (hz'.trans hz.symm)
      exact hw
  have unitζ : ∀ (k : Type) [Field k] (β : cycAway M →+* k), IsUnit (β (zetaAway M)) := fun k _ β =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, GlobalTheory.HTSympCover.zetaAway_pow_self M hM0, map_one]) hM0
  refine ⟨Y, i.left ≫ τ, fun a => i ≫ e a, hY1, hY2, fun T t₁' lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hpow, hgeo⟩ := hL
    obtain ⟨u, hu, huu⟩ := huniv T lv hadd hpow
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hSu T.left T.hom t₁'
    let v : T ⟶ S' := Over.homMk g hg1
    let w : T ⟶ W := lift u v
    have hwe : ∀ a, w ≫ e a = lv a := fun a => by
      simp only [w, e]
      rw [← Category.assoc, lift_fst, hu]
    have hwτ : w.left ≫ τ = t₁' := by
      simp only [τ]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact hg2
    have hr : Set.range w.left ⊆ U := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left q
      obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (x ≫ t₁')
      have hm : (x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs := by
        refine (memIff T w k x β (unitζ k β).unit (by rw [Category.assoc, hwτ, hβ]) rfl).2 ?_
        have := hgeo k x β (unitζ k β).unit hβ rfl
        simp only [hwe]
        exact this
      have hp' : x (default : PrimeSpectrum k) = q := by
        have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
        rwa [hx] at this
      exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left q by rw [← hp']; rfl) ▸ hm
    obtain ⟨f, hf⟩ := (Hi T w).1 hr
    refine ⟨f, ⟨by rw [← Category.assoc, ← Over.comp_left, hf, hwτ], fun a => by
      rw [← Category.assoc, hf, hwe]⟩, fun f' ⟨hf'1, hf'2⟩ => ?_⟩
    have e1 : f' ≫ i ≫ fst Z S' = u := huu _ fun a => by
      have := hf'2 a
      simp only [e, Category.assoc] at this ⊢
      exact this
    have e2 : f' ≫ i ≫ snd Z S' = v := by
      apply Over.OverMorphism.ext
      refine hgu _ ⟨Over.w (f' ≫ i ≫ snd Z S'), ?_⟩
      rw [← hf'1]
      simp [τ]
    have e3 : f' ≫ i = w := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, e1]; exact (lift_fst u v).symm
      · rw [Category.assoc, e2]; exact (lift_snd u v).symm
    exact (cancel_mono i).1 (e3.trans hf.symm)
  · obtain ⟨f, hf1, hf2⟩ := hex
    have hlv : ∀ a, lv a = (f ≫ i) ≫ e a := fun a => by rw [Category.assoc]; exact (hf2 a).symm
    refine ⟨fun a c => by rw [hlv, hlv, hlv, eadd', MonObj.comp_mul],
      fun a => by rw [hlv, ← MonObj.comp_pow, epow', MonObj.comp_one], fun k _ _ x β z hx hz => ?_⟩
    have hr : Set.range (f ≫ i).left ⊆ U := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hm : (x ≫ (f ≫ i).left) (default : PrimeSpectrum k) ∈ Vs := hr ⟨x (default : PrimeSpectrum k), rfl⟩
    have hG := (memIff T (f ≫ i) k x β z (by rw [← hx, ← hf1]; simp) hz).1 hm
    simp only [← hlv] at hG
    exact hG

end GlobalTheory.HTSympRep
