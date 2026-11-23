import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigidStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaStdAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricSymplecticLevelLiftSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTorsionOfWeilPairingFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectDeeperLevelOfSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem locEq : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit

theorem pairValue : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N → IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 → ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := GlobalTheory.DiagPairing.exists_weilIs_diag_root

theorem geomLift : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel

theorem geomBij : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := GlobalTheory.T.basis_torsion_of_weilPairing_field

theorem buildCover : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := GlobalTheory.T.exists_siegelObject_deeper_level_of_sections

open GlobalTheory.LevCover in

theorem exists_levelCover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  intro h n N B B' _ _ ζ b j S s' c hn hN hnN hζ hc
  have hNpos : 0 < N := hN.pos
  have hnodd : Odd n := hN.of_dvd_nat hnN
  have hNn : N / n * n = N := Nat.div_mul_cancel hnN
  let b₀ : TBase B' n :=
    { ζ := b.ζ ^ (N / n)
      unit := by
        have := b.unit
        rw [← hNn, Nat.cast_mul] at this
        exact isUnit_of_mul_isUnit_right this
      prim := fun K _ β => by
        rw [Units.val_pow_eq_pow_val, map_pow]
        exact (b.prim K β).pow hNpos hNn.symm }
  have hb₀ : (b₀.ζ : B') = (b.ζ : B') ^ (N / n) := Units.val_pow_eq_pow_val _ _
  have hj : j ζ = (b₀.ζ : B') := hζ.trans hb₀.symm
  have RC := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B B' ζ (b₀.ζ : B') j S S (s' ≫ spMap j) s' (𝟙 S) hj
    (Category.id_comp _)
  obtain ⟨c₀, hpb⟩ := RC.1 c
  have hc₀ : c₀.Principal := RC.2.1 c c₀ hpb hc
  have hrel : ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')),
      SRel C' c₀ (N / n) 1 t ↔ SRel C' c (N / n) 1 t := fun T t C' => by
    have := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N B B' B' ζ (b₀.ζ : B') (b.ζ : B') S S T (s' ≫ spMap j) s' (t ≫ s') c c₀ C'
      (𝟙 S) t 1 1 (N / n) ((sRel_one_one_iff c₀ c (𝟙 S)).2 hpb)).1
    rwa [Category.comp_id] at this
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (fnOn s')
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, hadd, hpow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S c₀.A N (Fin h ⊕ Fin h → ℤ) c₀.ab hNS
  have R : RepTors c₀.A N _ Z et := ⟨hfin, het, hadd, hpow, huniv⟩
  haveI := hfin
  haveI := het
  have hNZ : IsUnit (N : Γ(Z.left, ⊤)) := by
    have := hNS.map Z.hom.appTop.hom
    rwa [map_natCast] at this
  have hlevN : ∀ a, c₀.lev a ^ N = 1 := fun a => by
    rw [← hNn, mul_comm, pow_mul, c₀.lev_tors, one_pow]
  obtain ⟨Ul, hUl, HUl⟩ := R.clopenCond (fun a => et a ^ (N / n)) (fun a => toUnit Z ≫ c₀.lev a)
    (fun a a' => by rw [hadd, mul_pow]) (fun a => by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow])
    (fun a a' => by rw [c₀.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hlevN, MonObj.comp_one])
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : c₀.diag.IsLB := pull_isLB c₀.isLB _
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a a' k _ _ g =>
    ∀ β : B' →+* k, g ≫ Z.hom ≫ s' = spMap β →
      Out.WeilIs c₀.A c₀.diag N ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a)
        ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a')
        (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a')))
  have hzN : ∀ (k : Type) [Field k] (β : B' →+* k), Units.map β.toMonoidHom b.ζ ^ N = 1 := fun k _ β =>
    Units.ext (by simpa using (b.prim k β).pow_eq_one)
  have locPair : ∀ a a', HkClopen.Loc (P2 a a') := fun a a' => by
    obtain ⟨v, hv, hW⟩ := pairValue h n B' _ S s' c₀ N Z (et a) (et a') hc₀.1 hNpos hNZ (hpow a) (hpow a')
    refine (locEq Z.left N v (Units.map (fnOn (Z.hom ≫ s')).toMonoidHom (b.ζ ^ (2 * omegaStd a a'))) hNZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      rw [map_fnOn _ g β hβ, ← unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hzN, one_zpow]
      exact unitOn_one'
    · have hW' := CommPairing.weilIs_pull hG c₀.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      have hu := map_fnOn _ g β hβ (b.ζ ^ (2 * omegaStd a a'))
      rw [show Units.map β.toMonoidHom (b.ζ ^ (2 * omegaStd a a')) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') from map_zpow _ _ _] at hu
      constructor
      · intro e β' hβ'
        obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans hβ)
        rw [← hu, ← e]
        exact hW'
      · intro H
        exact CommutatorPairing.weilIs_unique hG c₀.ab hLB hW' (hu ▸ H β hβ)

  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hNpos
  haveI := hκ
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + N • c₁) (a' + N • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β hβ
    have e1 : ∀ a c, et (a + N • c) = et a := fun a c => by rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
    rw [e1, e1]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + N • c₁) (a' + N • c₂) = omegaStd a a' + N * m :=
      ⟨_, omegaStd_add_nsmul N a a' c₁ c₂⟩
    have hz : Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd (a + N • c₁) (a' + N • c₂)) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (N * m) = N * (2 * m) by ring, zpow_mul _ (N : ℤ), zpow_natCast,
        hzN, one_zpow, _root_.mul_one]
    rw [hz]
    exact H β hβ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨Wp, hWp, HWp⟩ := localization₂
  let U : Z.left.Opens := Ul ⊓ ⟨Wp, hWp.isOpen⟩
  have hU : IsClosed (U : Set Z.left) := hUl.inter hWp.isClosed
  obtain ⟨V, i, hV1, hV2, hi, Hi⟩ := exists_sub U hU
  have memWp : ∀ (Tw : Over S) (w : Tw ⟶ Z), (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Tw.left) (a a'),
      P2 a a' k (x ≫ w.left)) → Set.range w.left ⊆ Wp := by
    rintro Tw w H _ ⟨p, rfl⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point Tw.left p
    have h₁ := (HWp k (x ≫ w.left)).2 (H k x)
    have hp : x (default : PrimeSpectrum k) = p := by
      have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at this
    exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left p by rw [← hp]; rfl) ▸ h₁
  have hir : Set.range i.left ⊆ U := (Hi V i).2 ⟨𝟙 _, Category.id_comp _⟩
  have hiL := (HUl V i).2 fun _ hp => (hir hp).1
  have iW : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V.left) (a a'), P2 a a' k (x ≫ i.left) :=
    fun k _ _ x => (HWp k (x ≫ i.left)).1 (hir ⟨x (default : PrimeSpectrum k), rfl⟩).2

  have hprim : ∀ (k : Type) [Field k] (β : B' →+* k), IsPrimitiveRoot (Units.map β.toMonoidHom b.ζ) N :=
    fun k _ β => IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
  obtain ⟨C, φ, hsrel, hlev, huniv'⟩ := buildCover h n N (N / n) B' B' (b₀.ζ : B') (b.ζ : B') S V.left s'
    (V.hom ≫ s') V.hom c₀ (fun a => i ≫ et a) (fun a a' => by rw [hadd, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one])
    (fun a => by rw [← MonObj.comp_pow, hiL a, comp_toUnit_assoc]; rfl)
    (fun k _ _ x β z hx hz => by
      obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hz
      have hxS : (x ≫ V.hom) ≫ s' = spMap β := by rw [Category.assoc]; exact hx
      obtain ⟨e₀, a1, -, -, k1, o1, -⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k (x ≫ V.hom) β hn hN hnN hb₀
        hc₀ hxS
      have hpair : ∀ a a', Out.WeilIs c₀.A c₀.diag N
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a)
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a')
          (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := fun a a' =>
        weilIs_congr_base (by rw [Category.assoc, Over.w i]) (by simp) (by simp)
          (iW k x a a' β (by rw [← hx, Category.assoc, reassoc_of% (Over.w i)]))
      obtain ⟨b1, b2⟩ := geomBij h N k S (x ≫ V.hom) c₀.A c₀.diag (Units.map β.toMonoidHom b.ζ) e₀
        (fun a => (Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a) hLB hN (hprim k β) a1 k1 o1
        (fun a a' => by simp only [hadd, MonObj.comp_mul])
        (fun a => by rw [← MonObj.comp_pow, ← MonObj.comp_pow, hpow, MonObj.comp_one, MonObj.comp_one]) hpair
      exact ⟨b1, b2, hpair⟩)

  have h1T : ∀ (T : Scheme.{0}), (𝟙_ (Over T)).hom = 𝟙 T := fun T => rfl
  refine ⟨V.left, V.hom, C, hV1, hV2, ⟨fun pt => ?_⟩, (hrel V.left V.hom C).1 ⟨φ, hsrel⟩, fun T t C' hC' => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s')
    obtain ⟨e₀, a1, p1, l1, -, -, w1⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k x β hn hN hnN hb₀ hc₀ hβ
    obtain ⟨w, hw, -⟩ := huniv (Over.mk x) e₀ a1 p1
    have hx' : w.left ≫ Z.hom = x := Over.w w
    have hwl : Set.range w.left ⊆ Ul := (HUl (Over.mk x) w).1 fun a => by
      rw [MonObj.comp_pow, hw, l1, comp_toUnit_assoc]
    have hwW : w.left (default : PrimeSpectrum k) ∈ Wp := (HWp k w.left).2 fun a a' β' hβ' => by
      obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans (by rw [← Category.assoc, hx', hβ]))
      exact weilIs_congr_base hx'.symm (by rw [← hw a]; rfl) (by rw [← hw a']; rfl) (w1 a a')
    obtain ⟨w', hw'⟩ := (Hi _ w).1 fun _ hq => ⟨hwl hq, (HkClopen.range_subset_iff w.left Wp).2 hwW hq⟩
    obtain ⟨p, hp⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨w'.left p, by rw [← Scheme.Hom.comp_apply, Over.w w']; exact hp⟩
  · obtain ⟨φ', pb', hφ', low'⟩ := (hrel T t C').2 hC'
    let Tt : Over S := Over.mk ((𝟙_ (Over T)).hom ≫ t)
    let et' : (Fin h ⊕ Fin h → ℤ) → (Tt ⟶ c₀.A) := fun a => pushHom pb' (𝟙_ (Over T)) (C'.lev a)
    have a' : ∀ a a₂, et' (a + a₂) = et' a * et' a₂ := fun a a₂ => by simp only [et', C'.lev_add, map_mul]
    have p' : ∀ a, et' a ^ N = 1 := fun a => by simp only [et', ← map_pow, C'.lev_tors, map_one]
    obtain ⟨u, hu, -⟩ := huniv Tt et' a' p'
    have hul : ∀ a, (u ≫ et a).left = (C'.lev a).left ≫ φ' := fun a => by rw [hu]; rfl
    have hut : u.left ≫ Z.hom = t := (Over.w u).trans (Category.id_comp t)
    have hulow : Set.range u.left ⊆ Ul := (HUl Tt u).1 fun a => by
      rw [MonObj.comp_pow, hu, comp_toUnit_assoc]
      apply Over.OverMorphism.ext
      simp only [et', ← map_pow]
      show (C'.lev a ^ (N / n)).left ≫ φ' = (toUnit Tt).left ≫ (c₀.lev a).left
      rw [low' a, pow_one, Over.toUnit_left]
      exact (Category.id_comp t ▸ rfl : t ≫ (c₀.lev a).left = Tt.hom ≫ (c₀.lev a).left)
    have huW : Set.range u.left ⊆ Wp := memWp Tt u fun k _ _ x a a₂ β hβ =>
      weilTransport h N n B' B' (b₀.ζ : B') (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' pb' hφ' k x β
        (Units.map β.toMonoidHom b.ζ) ((x ≫ u.left) ≫ Z.hom) _ _ a a₂
        (by rw [← hβ, Category.assoc, reassoc_of% hut])
        rfl (by rw [Category.assoc, hut])
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
    obtain ⟨t₁, ht₁⟩ := (Hi Tt u).1 fun _ hq => ⟨hulow hq, huW hq⟩
    have ht₁π : t₁.left ≫ V.hom = t := (Over.w t₁).trans (Category.id_comp t)
    refine ⟨t₁.left, ⟨ht₁π, (huniv' T t₁.left B' (b.ζ : B') (t ≫ s') C').2 ⟨φ', by rw [ht₁π]; exact ⟨pb', hφ', low'⟩,
      fun a => (hul a).symm.trans (by rw [← ht₁]; simp)⟩⟩, ?_⟩
    rintro t₂ ⟨ht₂, hpb₂⟩
    obtain ⟨φ₂, hsr₂, hl₂⟩ := (huniv' T t₂ B' (b.ζ : B') (t ≫ s') C').1 hpb₂
    rw [ht₂] at hsr₂
    have e := GlobalTheory.T.principal_siegel_object_odd_level_rigid h n N (N / n) B' B' b₀ (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' φ₂ hn hnodd hc₀
      ⟨pb', hφ', low'⟩ hsr₂
    subst e
    let h₂ : Tt ⟶ V := Over.homMk t₂ (ht₂.trans (Category.id_comp t).symm)
    have : h₂ ≫ i = u := R.ext fun a => Over.OverMorphism.ext (by rw [hul, hl₂ a]; simp [h₂])
    exact congrArg (fun q => q.left) ((cancel_mono i).1 (this.trans ht₁.symm))

end GlobalTheory.SiegCover
