import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def uIdeal (D : Datum p) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

theorem p_mem_uIdeal (D : Datum p) (r : ℤ) : (p : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem sub_mem_uIdeal (D : Datum p) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem exists_prime_uIdeal_le (D : Datum p) : ∃ (r : ℤ) (w : Ideal (𝓞 D.F)), w.IsMaximal ∧ uIdeal D r ≤ w := by
  obtain ⟨r, k, hk⟩ := D.split
  refine ⟨r, Ideal.exists_le_maximal _ fun htop => ?_⟩
  have h1 : (1 : 𝓞 D.F) ∈ uIdeal D r := htop ▸ Submodule.mem_top
  obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.1 h1
  have hk' : ((r : 𝓞 D.F)) ^ 2 - (D.tr : 𝓞 D.F) * r + D.nm = (p : 𝓞 D.F) * k := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.F) hk
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hbb : D.bar (D.bar D.ω) = D.ω := by
    have := congrArg D.bar htr
    rw [map_add, map_intCast] at this
    linear_combination this - htr
  have e1 : D.bar D.ω - r = (p : 𝓞 D.F) * (a * (D.bar D.ω - r) + c * k) := by
    linear_combination (-(D.bar D.ω - r)) * hac + c * hk' + c * hnm - c * r * htr
  set u := a * (D.bar D.ω - r) + c * k
  have e2 : D.ω - r = (p : 𝓞 D.F) * D.bar u := by
    have := congrArg D.bar e1
    rwa [map_sub, map_mul, map_intCast, map_natCast, hbb] at this
  have e3 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : 𝓞 D.F) = (p : 𝓞 D.F) * ((D.bar u - u) * (D.ω - D.bar D.ω)) := by
    push_cast
    linear_combination (D.ω - D.bar D.ω) * (e2 - e1) - (D.ω + D.bar D.ω + D.tr) * htr + 4 * hnm
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  obtain ⟨x, y, hxy⟩ := (hp.coprime_iff_not_dvd.2 D.disc_p)
  have hu : IsUnit (algebraMap ℤ (𝓞 D.F) (p : ℤ)) := by
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, e3, Int.cast_one, Int.cast_natCast] at h
    refine IsUnit.of_mul_eq_one ((x : 𝓞 D.F) + y * ((D.bar u - u) * (D.ω - D.bar D.ω))) ?_
    simp only [eq_intCast, Int.cast_natCast]
    linear_combination h
  exact hp.not_unit (isUnit_of_map_unit _ _ hu)

def IsPIsog {N : ℕ} {s : S ⟶ Sp R} (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  (∃ k : ℕ, c = p ^ k) ∧
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta x ≫ ψ) ∧
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ∧
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

theorem IsPIsog.exists_eq_pow {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : ∃ k : ℕ, c = p ^ k := h.1

theorem IsPIsog.pos {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : 0 < c := by
  obtain ⟨k, rfl⟩ := h.1
  exact pow_pos (Fact.out : p.Prime).pos k

def KilledBy {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over S} (g : T ⟶ o.A) : Prop :=
  ∀ a ∈ v, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1

def IsTj {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S),
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

structure TjCorr {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) where

  Y : Scheme.{0}

  s : Y ⟶ F.X

  t : Y ⟶ F.X
  st : s ≫ F.s = t ≫ F.s

  o : Obj b N (s ≫ F.s)

  o' : Obj b N (s ≫ F.s)
  ms : ObjMap o F.univ s
  mt : ObjMap o' F.univ t

  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ

  wPrime : w.IsPrime

  uLe : uIdeal D r ≤ w

  pReg : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0

  sFin : IsFinite s

  tFin : IsFinite t

  sSurj : Surjective s

theorem TjCorr.p_mem {N : ℕ} {F : RepFam b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjCorr F r w j c) :
    (p : 𝓞 D.F) ∈ w :=
  T.uLe (p_mem_uIdeal D r)

theorem TjCorr.w_ne_top {N : ℕ} {F : RepFam b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjCorr F r w j c) :
    w ≠ ⊤ :=
  T.wPrime.ne_top

theorem exists_charZero_point (b : Base D R) {Y : Scheme.{0}} (s : Y ⟶ Sp R)
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0) (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (x : Sp k ⟶ Y), ∀ q, x q ∈ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  have hnil : ¬ IsNilpotent (p : Γ(Y, V)) := by
    rintro ⟨n, hn⟩
    induction n with
    | zero => exact one_ne_zero (by rwa [pow_zero] at hn)
    | succ n ih => exact ih (hp V _ (by rwa [pow_succ'] at hn))
  obtain ⟨P, hP, hpP⟩ : ∃ P : Ideal Γ(Y, V), P.IsPrime ∧ (p : Γ(Y, V)) ∉ P := by
    by_contra h
    push Not at h
    exact hnil (nilpotent_iff_mem_prime.2 h)
  let k := AlgebraicClosure P.ResidueField
  let φ : Γ(Y, V) →+* k := (algebraMap P.ResidueField k).comp (algebraMap _ P.ResidueField)
  have hpk : (p : k) ≠ 0 := by
    rw [← map_natCast φ]
    intro h
    exact hpP (Ideal.algebraMap_residueField_eq_zero.1 ((algebraMap P.ResidueField k).injective
      (h.trans (map_zero _).symm)))
  let x : Sp k ⟶ Y := Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  haveI : CharZero k := by
    haveI := ringChar.charP k
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
    · exfalso
      have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
      by_cases h : ringChar k = p
      · exact hpk (h ▸ h0)
      · have := (b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)).map β
        rw [map_natCast, h0] at this
        exact not_isUnit_zero this
    · haveI : CharP k 0 := hl ▸ ringChar.charP k
      exact CharP.charP_to_charZero k
  refine ⟨k, inferInstance, inferInstance, inferInstance, x, fun q => hVU ?_⟩
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

theorem TjCorr.exists_charZero_point {N : ℕ} {F : RepFam b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}
    (T : TjCorr F r w j c) (U : T.Y.Opens) (y : T.Y) (hy : y ∈ U) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (x : Sp k ⟶ T.Y), ∀ q, x q ∈ U :=
  ES.exists_charZero_point b (T.s ≫ F.s) T.pReg U y hy

theorem TjCorr.eq_of_isTj {N : ℕ} {F : RepFam b N} [Nonempty F.X] {r : ℤ} {w : Ideal (𝓞 D.F)} {j c j' : ℕ}
    (T : TjCorr F r w j c) (h : IsTj r w j' T.o T.o' T.ψ) : j' = j := by
  obtain ⟨y, -⟩ := T.sSurj.surj (Classical.arbitrary F.X)
  obtain ⟨k, _, _, _, x, -⟩ := T.exists_charZero_point ⊤ y trivial
  have e := (h k x).2.symm.trans (T.tj k x).2
  have h0 : Ideal.absNorm w ≠ 0 := fun h0 => by
    have hp := T.p_mem
    rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp
  have h1 : Ideal.absNorm w ≠ 1 := fun h1 => T.w_ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  exact Nat.eq_of_mul_eq_mul_left D.m_pos (Nat.pow_right_injective (by omega) e)

theorem IsPIsog.id {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) : IsPIsog 1 o o (𝟙 o.A) := by
  have e : sq2 (𝟙 o.A) = 𝟙 (G2 o.A).left := by
    simp only [sq2, Category.comp_id, lift_fst_snd]; rfl
  refine ⟨⟨0, (pow_zero p).symm⟩, inferInstance, fun c' => ?_, fun x => (Category.comp_id _).symm, ?_, 𝟙 o.A,
    inferInstance, ?_, ?_⟩
  · rw [Category.comp_id, Category.id_comp]
  · refine ⟨(GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 ?_⟩
    show _ = ∏ _k : PUnit, GlobalTheory.PrimNorm.cls o.P (sq2 (𝟙 o.A)) ^ (1 : ℤ)
    rw [e]
    simp
  · rw [pow_one, Category.comp_id]
  · rw [pow_one, Category.comp_id]

theorem KilledBy.one {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) (T : Over S) :
    KilledBy o v (1 : T ⟶ o.A) := fun a _ => by
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
  exact one_comp _

theorem IsTj.id {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (o : Obj b N s) :
    IsTj r w 0 o o (𝟙 o.A) := by
  intro k _ _ _ x
  refine ⟨fun g hg _ => ?_, ?_⟩
  · rw [Category.comp_id] at hg
    subst hg
    exact KilledBy.one o w _
  · rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, by rw [Category.comp_id], KilledBy.one o w _⟩, fun y => Subtype.ext ?_⟩
    have := y.2.1
    rw [Category.comp_id] at this
    exact this

theorem exists_tjCorr_diag {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w.IsPrime)
    (hu : uIdeal D r ≤ w) (hp : ∀ (U : F.X.Opens) (f : Γ(F.X, U)), (p : Γ(F.X, U)) * f = 0 → f = 0) :
    ∃ T : TjCorr F r w 0 1, IsIso T.s ∧ IsIso T.t ∧ IsIso T.ψ := by
  obtain ⟨o, ⟨m⟩⟩ : ∃ o : Obj b N (𝟙 F.X ≫ F.s), Nonempty (ObjMap o F.univ (𝟙 F.X)) := by
    rw [Category.id_comp]
    exact ⟨F.univ, ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id F.univ.A
                      sq := ⟨by simp, by simp⟩, act := fun c => by simp
                      pol := GlobalTheory.SiegLower.lbIso_pull_id F.univ.isLB, eta := fun y => by simp }⟩⟩
  exact ⟨⟨F.X, 𝟙 _, 𝟙 _, rfl, o, o, m, m, 𝟙 o.A, IsPIsog.id o, IsTj.id r w o, hw, hu, hp, inferInstance,
    inferInstance, inferInstance⟩, inferInstanceAs (IsIso (𝟙 F.X)), inferInstanceAs (IsIso (𝟙 F.X)),
    inferInstanceAs (IsIso (𝟙 o.A))⟩

theorem pReg_of_flat {Y : Scheme.{0}} (s : Y ⟶ Sp R) [Flat s] (hR : ∀ a : R, (p : R) * a = 0 → a = 0)
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · have hfl : (s.appLE ⊤ V.1.1 le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ V.1 le_top
    have hp : (p : Γ(Sp R, ⊤)) ∈ nonZeroDivisors Γ(Sp R, ⊤) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro a ha
      let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      refine e.injective ((hR _ ?_).trans (map_zero e).symm)
      rw [← map_natCast e, ← map_mul, ha, map_zero]
    letI := (s.appLE ⊤ V.1.1 le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V.1.1) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Y, V.1.1)) hp
    let ρ : Γ(Y, U) →+* Γ(Y, V.1.1) := (Y.presheaf.map (homOfLE V.2).op).hom
    show ρ f = ρ 0
    refine hreg ?_
    simp only [Algebra.smul_def, map_natCast, map_zero, mul_zero]
    rw [← map_natCast ρ, ← map_mul, hf, map_zero]

theorem pReg_of_isUnit {Y : Scheme.{0}} (s : Y ⟶ Sp R) (hR : IsUnit (p : R))
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  have := hR.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U le_top).hom)
  rw [map_natCast] at this
  exact this.mul_right_eq_zero.1 hf

theorem exists_tjCorr_diag_model {N : ℕ} (M : Model b N) (hR : ∀ a : R, (p : R) * a = 0 → a = 0) :
    ∃ (r : ℤ) (w : Ideal (𝓞 D.F)) (T : TjCorr M.toRepFam r w 0 1), IsIso T.s ∧ IsIso T.t ∧ IsIso T.ψ := by
  obtain ⟨r, w, hw, hu⟩ := exists_prime_uIdeal_le D
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  exact ⟨r, w, exists_tjCorr_diag M.toRepFam r w hw.isPrime hu (fun U f hf => pReg_of_flat (Y := M.X) M.s hR U f hf)⟩

def IsWOrd {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {k : Type} [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : Prop :=
  CharP k p ∧ w.IsPrime ∧ (p : 𝓞 D.F) ∈ w ∧
    Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1))

theorem isWOrd_iff {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) {r : ℤ} {w : Ideal (𝓞 D.F)} (hw : w.IsPrime)
    (hu : uIdeal D r ≤ w) {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (x : Sp k ⟶ S) :
    IsWOrd o w x ↔
      Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1)) :=
  ⟨fun h => h.2.2.2, fun h => ⟨inferInstance, hw, hu (p_mem_uIdeal D r), h⟩⟩

example (w : Ideal (𝓞 D.F)) (j : ℕ) (h : D.m = 1) : Ideal.absNorm w ^ (D.m * j) = Ideal.absNorm w ^ j := by
  rw [h, Nat.one_mul]

example (w : Ideal (𝓞 D.F)) : Ideal.absNorm w ^ (D.m * 0) = 1 := by simp

example : ∃ k : ℕ, (1 : ℕ) = p ^ k := ⟨0, (pow_zero p).symm⟩

end GlobalTheory.UPel.HT.ES
