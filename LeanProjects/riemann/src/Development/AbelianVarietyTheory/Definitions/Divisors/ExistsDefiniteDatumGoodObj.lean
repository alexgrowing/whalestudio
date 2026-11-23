import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsComplexCmAbelianObject

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable (F : Type) [Field F] [NumberField F] [IsCMField F]

structure Datum where
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  w : 𝓞 F
  w_add : w + bar w = 1
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 F) La]
  fin : Module.Finite (𝓞 F) La
  proj : Module.Projective (𝓞 F) La
  n : ℕ
  rank : Module.finrank (𝓞 F) La = n
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 F) x y, EF (a • x) y = EF x (bar a • y)
  sig : (F →+* ℂ) → ℕ
  sig_conj : ∀ τ, sig τ + sig ((starRingEnd ℂ).comp τ) = n
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      J ∘ₗ A = A ∘ₗ J ∧
      LinearMap.trace ℝ _ A = 2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).re ∧
      LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).im

attribute [instance] Datum.acg Datum.mod

variable {F}

def Datum.reflex (D : Datum F) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun a : F => ∑ τ : F →+* ℂ, (D.sig τ : ℂ) * τ a)

def Datum.OEp (D : Datum F) (p : ℕ) : Subring ℂ :=
  Subring.closure ({x | x ∈ D.reflex ∧ IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

def ZbarP (p : ℕ) : Subring ℂ :=
  Subring.closure ({x : ℂ | IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

theorem OEp_le (D : Datum F) (p : ℕ) : D.OEp p ≤ ZbarP p :=
  Subring.closure_mono (Set.union_subset_union (fun _ hx => hx.2) le_rfl)

def embP (p : ℕ) (τ : F →+* ℂ) (a : 𝓞 F) : ZbarP p :=
  ⟨τ (a : F), Subring.subset_closure (Or.inl ((NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom))⟩

variable {S : Scheme.{0}}

open Classical in

def DetCondP (D : Datum F) (p : ℕ) {k : Type} [Field k] {G : Over S} [GrpObj G] (act : OAct (𝓞 F) G)
    (x : Sp k ⟶ S) (β : D.OEp p →+* k) : Prop :=
  ∃ β' : ZbarP p →+* k, (∀ y : D.OEp p, β' (Subring.inclusion (OEp_le D p) y) = β y) ∧
    ∀ σ : 𝓞 F →+* k, LieMult act x σ
      (∑ τ ∈ (Finset.univ.filter fun τ : F →+* ℂ => ∀ a, β' (embP p τ a) = σ a), D.sig τ)

structure TateIsoP (D : Datum F) (p : ℕ) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 F → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n a b, ev n (a + b) = ev n a * ev n b
  lin : ∀ n (c : 𝓞 F) a, ev n (c • a) = act c (ev n a)
  ker : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = 1 ↔ ∃ b, a = n • b
  onto : ∀ n, 0 < n → n.Coprime p → ∀ x, x ^ n = 1 ↔ ∃ a, ev n a = x
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ a, ev (n * m) a ^ m = ev n a
  isom : ∀ n, 0 < n → n.Coprime p → ∀ a b, e n (ev n a) (ev n b) (ζ n ^ D.EF a b)

structure Obj (D : Datum F) (p N : ℕ) (s : S ⟶ Sp (D.OEp p)) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OAct (𝓞 F) A
  PP : RigLB A
  cub : CubicalStr A PP
  sym : PP.IsSymmetric
  adj : ∀ a, LBIso (cubeLB A ![fst A A ≫ act.act a, snd A A] PP.L)
    (cubeLB A ![fst A A, snd A A ≫ act.act (D.bar a)] PP.L)
  prim : LBIso PP.L (cubeLB A ![𝟙 A, act.act D.w] PP.L)
  ample : Out.RelAmple A PP.L
  ktriv : Out.KTriv A PP.L
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ a c, eta (a + c) = eta a * eta c
  eta_ker : ∀ a, eta (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : D.OEp p →+* k), x ≫ s = spMap β →
    DetCondP D p act x β ∧
    ∃ I : TateIsoP D p k (Over.mk x ⟶ A) (fun a g => g ≫ act.act a)
        (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)),
      ∀ a, toUnit _ ≫ eta a = I.ev N a

attribute [instance] Obj.grp Obj.comm

structure ObjMap {D : Datum F} {p N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp (D.OEp p)} {s : S ⟶ Sp (D.OEp p)}
    (o' : Obj D p N s') (o : Obj D p N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  cart : IsGrpPullback o'.A o.A f φ
  act : ∀ a, (o'.act.act a).left ≫ φ = φ ≫ (o.act.act a).left
  pol : LBIso o'.PP.L (o.PP.L.pull φ)
  eta : ∀ a, (o'.eta a).left ≫ φ = f ≫ (o.eta a).left

def Datum.dim (D : Datum F) : ℕ := (∑ τ : F →+* ℂ, D.sig τ * (D.n - D.sig τ)) / 2

structure IntModel (D : Datum F) (p N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (D.OEp p)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D p N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (D.OEp p)), IsReduced S → ∀ o : Obj D p N s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D p N (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x

def Good (F : Type) [Field F] [NumberField F] (p N : ℕ) : Prop :=
  p.Prime ∧ ¬ (p : ℤ) ∣ NumberField.discr F ∧ 3 ≤ N ∧ N.Coprime p

def Datum.Definite (D : Datum F) : Prop := ∃ τ : F →+* ℂ, D.sig τ = 0

def ObjMap.refl {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  cart := by
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
    let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
    have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
    rw [e₁, e₂, ← MonObj.comp_mul]
    simp [j]
  act a := by simp
  pol := (GlobalTheory.PolBaseChange.lbIso_refl o.PP.isLB).chartPull (Geo.Tor.chartPullId _)
    (Geo.Tor.chartPullPull _ _ _ rfl)
  eta a := by simp

theorem exists_good (F : Type) [Field F] [NumberField F] {N : ℕ} (hN : 3 ≤ N) : ∃ p, Good F p N := by
  obtain ⟨p, hp, hpr⟩ := Nat.exists_infinite_primes ((NumberField.discr F).natAbs + N + 1)
  refine ⟨p, hpr, fun h => ?_, hN, (Nat.coprime_of_lt_prime (by omega) (by omega) hpr).symm⟩
  have h₁ := Nat.le_of_dvd (Int.natAbs_pos.2 (NumberField.discr_ne_zero F)) (Int.natCast_dvd.1 h)
  omega

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem conj_mem_type_iff (H : Host E) (τ : E →+* ℂ) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 := by
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h1 => hd (by have h2 := H.sqrt_neg_disc_sq; rw [h1] at h2; linear_combination h2)
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, HostModel.coe_rt_sq, H.sqrt_neg_disc_sq]; simp
  rw [RingHom.comp_apply, HostModel.conj_embedding_rt]
  constructor
  · intro h h'
    rw [h'] at h
    exact h0 (by linear_combination (-1 / 2 : ℂ) * h)
  · intro h
    rw [(sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left h, neg_neg]

open Classical in

theorem sum_mult_eq (D : Geo.Tor.Datum H) (a : E) :
    ∑ τ : E →+* ℂ, (D.mult τ : ℂ) * τ a =
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ a + (D.q : ℂ) * starRingEnd ℂ (τ a)) := by
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Geo.Tor.Datum.mult, if_pos (Finset.mem_filter.1 hτ).2]
  · refine Finset.sum_nbij' (fun τ => (starRingEnd ℂ).comp τ) (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (conj_mem_type_iff H τ).2 hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact fun h => (conj_mem_type_iff H τ).1 h hτ
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ hτ
      rw [Geo.Tor.Datum.mult, if_neg (Finset.mem_filter.1 hτ).2]
      simp

@[reducible] def Datum.ofHost (D : Geo.Tor.Datum H) : Datum E where
  bar := H.bar
  bar_eq := H.bar_eq
  w := H.w0
  w_add := by rw [HostModel.cmHost_bar_halfIntegerGenerator]; ring
  La := D.La
  fin := D.fin
  proj := D.proj
  n := D.p + D.q
  rank := D.rank
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := D.adj
  sig := D.mult
  sig_conj τ := by
    unfold Geo.Tor.Datum.mult
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun h' => (conj_mem_type_iff H τ).1 h' h]
    · rw [if_neg h, if_pos ((conj_mem_type_iff H τ).2 h), add_comm]
  dom := by
    obtain ⟨J, h₁, h₂, h₃, h₄⟩ := D.dom
    exact ⟨J, h₁, h₂, h₃, fun a A hA => h₄ a A _ hA (by convert sum_mult_eq D (a : E))⟩

theorem dim_ofHost (D : Geo.Tor.Datum H) : (Datum.ofHost D).dim = D.dim := by
  have h : ∀ τ : E →+* ℂ, D.mult τ * (D.p + D.q - D.mult τ) = D.p * D.q := fun τ => by
    unfold Geo.Tor.Datum.mult
    split_ifs
    · rw [Nat.add_sub_cancel_left]
    · rw [Nat.add_sub_cancel, mul_comm]
  unfold Datum.dim Geo.Tor.Datum.dim
  simp only [h, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]
  rw [IsTotallyComplex.finrank E, Nat.mul_assoc, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos,
    Nat.mul_assoc]

theorem definite_ofHost_iff (D : Geo.Tor.Datum H) : (Datum.ofHost D).Definite ↔ D.p = 0 ∨ D.q = 0 := by
  obtain ⟨τ₀, h₀⟩ := HostModel.exists_embedding_rt_eq H
  constructor
  · rintro ⟨τ, hτ⟩
    change D.mult τ = 0 at hτ
    unfold Geo.Tor.Datum.mult at hτ
    split_ifs at hτ
    exacts [Or.inl hτ, Or.inr hτ]
  · rintro (h | h)
    · exact ⟨τ₀, (if_pos h₀).trans h⟩
    · exact ⟨(starRingEnd ℂ).comp τ₀, (if_neg fun h' => (conj_mem_type_iff H τ₀).1 h' h₀).trans h⟩

def TateIsoP.ofHost {D : Geo.Tor.Datum H} (p : ℕ) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) : TateIsoP (Datum.ofHost D) p k Q act e where
  ζ := I.ζ
  ζ_prim n hn _ := I.ζ_prim n hn
  ζ_pow n m hn hm _ := I.ζ_pow n m hn hm
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n hn _ := I.ker n hn
  onto n hn _ := I.onto n hn
  tower n m hn hm _ := I.tower n m hn hm
  isom n hn _ := I.isom n hn

omit [IsCMField E] in

theorem existsUnique_embedding {k : Type} [Field k] [IsAlgClosed k] (ξ : ℂ →+* k) (σ : 𝓞 E →+* k) :
    ∃! τ : E →+* ℂ, ∀ a : 𝓞 E, ξ (τ (a : E)) = σ a := by
  haveI : CharZero k := ξ.charZero_iff ξ.injective |>.1 inferInstance
  have hi : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))
  have hinj : Function.Injective fun τ : E →+* ℂ => ξ.comp τ := fun τ τ' h =>
    RingHom.ext fun x => ξ.injective (RingHom.congr_fun h x)
  have hbij : Function.Bijective fun τ : E →+* ℂ => ξ.comp τ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by
      rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  obtain ⟨τ, hτ⟩ := hbij.2 (IsFractionRing.lift (K := E) hi)
  refine ⟨τ, fun a => (RingHom.congr_fun hτ a).trans (IsFractionRing.lift_algebraMap hi a), fun τ' h => hinj ?_⟩
  rw [hτ]
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    (RingHom.ext fun a => (h a).trans (IsFractionRing.lift_algebraMap hi a).symm)

theorem determinantConditionAt_of_determinantCondition (D : Geo.Tor.Datum H) (p : ℕ) {k : Type} [Field k] [IsAlgClosed k] {G : Over S} [GrpObj G]
    (act : OAct (𝓞 E) G) (x : Sp k ⟶ S) (ξ : ℂ →+* k) (h : DetCond D act x (ξ H.rt0)) :
    DetCondP (Datum.ofHost D) p act x (ξ.comp ((Datum.ofHost D).OEp p).subtype) := by
  refine ⟨ξ.comp (ZbarP p).subtype, fun y => ?_, fun σ => ?_⟩
  · simp only [RingHom.comp_apply, Subring.coe_subtype, Subring.coe_inclusion]
  obtain ⟨τ, hτ, huniq⟩ := existsUnique_embedding ξ σ
  have key : LieMult act x σ (D.mult τ) := by
    unfold Geo.Tor.Datum.mult
    split_ifs with hr
    · exact (h σ).1 (by rw [← hτ, hr])
    · exact (h σ).2 (by rw [← hτ]; exact fun h' => hr (ξ.injective h'))
  have he : ∀ τ' : E →+* ℂ, (∀ a, (ξ.comp (ZbarP p).subtype) (embP p τ' a) = σ a) ↔ τ' = τ := fun τ' =>
    ⟨fun h' => huniq τ' h', fun h' => h' ▸ hτ⟩
  rw [Finset.sum_eq_single_of_mem τ]
  · exact key
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  · intro τ' h' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he] at h'
    exact absurd h' hne

def Obj.ofHost {D : Geo.Tor.Datum H} {l : Level H} {b : Base l ℂ} (hb : b.ρ = H.rt0) (p : ℕ) {s : S ⟶ Sp ℂ}
    (o : Geo.Tor.Obj D l b s) :
    Obj (Datum.ofHost D) p l.A (s ≫ spMap ((Datum.ofHost D).OEp p).subtype) where
  A := o.t.G
  ab := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  act := o.t.act
  PP := o.t.PP
  cub := o.t.cub
  sym := o.t.sym
  adj := o.t.adj
  prim := o.t.prim
  ample := o.ample
  ktriv := o.ktriv
  eta := o.etaA
  eta_add := o.etaA_add
  eta_ker := o.etaA_ker
  geom k _ _ x β hx := by
    obtain ⟨ξ, hξ⟩ : ∃ ξ : ℂ →+* k, x ≫ s = spMap ξ :=
      ⟨(Spec.preimage (x ≫ s)).hom, (Spec.map_preimage _).symm⟩
    obtain rfl : β = ξ.comp ((Datum.ofHost D).OEp p).subtype := by
      rw [← Category.assoc, hξ] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective
        (hx.symm.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm))
    obtain ⟨hdet, I, -, hI, -⟩ := o.geom k x ξ hξ
    exact ⟨determinantConditionAt_of_determinantCondition D p _ x ξ (hb ▸ hdet), TateIsoP.ofHost p I, hI⟩

theorem exists_obj_ofHost (D : Geo.Tor.Datum H) (hD : 1 ≤ D.p + D.q) (p N : ℕ) (hN : 0 < N) :
    ∃ o : Obj (Datum.ofHost D) p N (𝟙 (Sp ℂ) ≫ spMap ((Datum.ofHost D).OEp p).subtype),
      SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Datum.ofHost D).n) o.A.hom ∧
        ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.A, x ≠ 1 := by
  obtain ⟨b, o, hb, -, h⟩ := GlobalTheory.exists_obj_complex E H D hD (HostModel.level H N hN)
  exact ⟨Obj.ofHost hb p o, h⟩

end Host

theorem exists_datum_good_obj : ∃ (D : Datum HostModel.E21) (p : ℕ), D.n = 2 ∧ D.dim = 6 ∧ Good HostModel.E21 p 5 ∧
    ∃ o : Obj D p 5 (𝟙 (Sp ℂ) ≫ spMap (D.OEp p).subtype), SmoothOfRelativeDimension 12 o.A.hom ∧
      ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.A, x ≠ 1 := by
  obtain ⟨p, hp⟩ := exists_good HostModel.E21 (N := 5) (by norm_num)
  refine ⟨Datum.ofHost (HostModel.hypDatum HostModel.host), p, rfl, ?_, hp, ?_⟩
  · rw [dim_ofHost, Geo.Tor.Datum.dim, HostModel.finrank_rat_E21_eq_twelve]; rfl
  · have h := exists_obj_ofHost (HostModel.hypDatum HostModel.host) (by norm_num) p 5 (by norm_num)
    rw [HostModel.finrank_rat_E21_eq_twelve] at h
    exact h

theorem exists_definite_datum_good_obj : ∃ (D : Datum CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight) (p : ℕ), D.n = 1 ∧ D.dim = 0 ∧ D.Definite ∧
    Good CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight p 5 ∧ ∃ o : Obj D p 5 (𝟙 (Sp ℂ) ≫ spMap (D.OEp p).subtype),
      ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.A, x ≠ 1 := by
  obtain ⟨p, hp⟩ := exists_good CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight (N := 5) (by norm_num)
  obtain ⟨D, h₁, h₀⟩ := CM.CyclotomicTwentyEight.exists_datum
  obtain ⟨o, -, ho⟩ := exists_obj_ofHost D (by omega) p 5 (by norm_num)
  refine ⟨Datum.ofHost D, p, ?_, ?_, (definite_ofHost_iff D).2 (Or.inr h₀), hp, o, ho⟩
  · change D.p + D.q = 1
    omega
  · rw [dim_ofHost, Geo.Tor.Datum.dim, h₀, Nat.mul_zero]

example (D : Datum F) : D.w ≠ 0 := fun h => by simpa [h] using D.w_add

example {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ¬ (Datum.ofHost (HostModel.hypDatum H)).Definite := by
  rw [definite_ofHost_iff]; simp

end GlobalTheory.UPel
