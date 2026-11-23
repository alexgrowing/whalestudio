import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.CechDeg

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w w'

section Abstract

variable {R : Type} [CommRing R]

def shC (K : DCx.{w} R) : DCx.{w} R where
  X p q := K.X (p + 1) q
  dh p q := K.dh (p + 1) q
  dv p q := - K.dv (p + 1) q
  hh p q := K.hh (p + 1) q
  vv p q x := by simp [K.vv]
  hv p q x := by simp [K.hv]

def Ex (K : DCx.{w} R) (a : ℕ) : Prop :=
  ∀ p, (0 < a → Function.Injective (K.dv p 0)) ∧
    ∀ q, q + 1 < a → ∀ x, K.dv p (q + 1) x = 0 → ∃ y, K.dv p q y = x

theorem Ex.sh {K : DCx.{w} R} {a : ℕ} (h : Ex K a) : Ex (shC K) a := by
  intro p
  refine ⟨fun ha x y hxy => (h (p + 1)).1 ha (neg_injective hxy), fun q hq x hx => ?_⟩
  obtain ⟨y, hy⟩ := (h (p + 1)).2 q hq x (neg_eq_zero.1 hx)
  exact ⟨-y, by simp [shC, hy]⟩

def sh (K : DCx.{w} R) (x : ∀ p q, K.X p q) : ∀ p q, (shC K).X p q := fun p q => x (p + 1) q

def un (K : DCx.{w} R) (y : ∀ p q, (shC K).X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | p + 1, q => y p q

theorem D_sh (K : DCx.{w} R) (x : ∀ p q, K.X p q) (h : ∀ q, x 0 q = 0) : (shC K).D (sh K x) = sh K (K.D x) := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sh, h]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sh, h, shC]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sh, shC]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sh, shC, pow_succ]

theorem D_un (K : DCx.{w} R) (y : ∀ p q, (shC K).X p q) : K.D (un K y) = un K ((shC K).D y) := by
  funext p q
  rcases p with _ | _ | p <;> rcases q with _ | q
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un, shC]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un, shC]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, un, shC, pow_succ]

theorem un_sh (K : DCx.{w} R) (x : ∀ p q, K.X p q) (h : ∀ q, x 0 q = 0) : un K (sh K x) = x := by
  funext p q
  rcases p with _ | p
  · exact (h q).symm
  · rfl

theorem vanish (K : DCx.{w} R) (a m : ℕ) (h : Ex K a) (hm : m < a) (x : ∀ p q, K.X p q) (hx : x ∈ K.T m)
    (hD : K.D x = 0) : ∃ z : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ m → z p q = 0) ∧ K.D z = x := by
  let A : Cx.{0} R := ⟨fun _ => PUnit, fun _ => 0, fun _ _ => rfl⟩
  let e : DCx.AugCol A K := ⟨fun _ => 0, fun _ _ => map_zero _, fun p x => by simp⟩
  have hs := P.dc_col_surj e 1 m
    (fun p q hpq y hy => by
      obtain ⟨t, ht⟩ := (h p).2 q (by omega) y hy
      exact ⟨t, by rw [one_smul, ht]⟩)
    (fun y hy => ⟨0, by rw [one_smul, map_zero]; exact ((h m).1 (by omega) (hy.trans (map_zero _).symm)).symm⟩)
    (fun y _ => Subsingleton.elim _ _)
  have hc : K.tot.d m ⟨x, hx⟩ = 0 := Subtype.ext hD
  obtain ⟨t, ht⟩ := hs (K.tot.cls ⟨x, hx⟩ hc)
  have ht0 : t = 0 := Subsingleton.elim _ _
  rw [ht0, map_zero, one_pow, one_smul] at ht
  have hB := ((P.cls_surj K.tot m).2.1 _ hc).1 ht.symm
  cases m with
  | zero =>
    have h0 : x = 0 := congrArg Subtype.val ((Submodule.mem_bot R).1 hB)
    exact ⟨0, fun _ _ _ => rfl, by rw [map_zero, h0]⟩
  | succ m =>
    obtain ⟨z, hz⟩ := hB
    exact ⟨z.1, fun p q hpq => z.2 p q (by omega), congrArg Subtype.val hz⟩

theorem tail (K : DCx.{w} R) (a n : ℕ) (h : Ex K a) (hn : n ≤ a) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n)
    (hD : K.D x = 0) (h0 : ∀ q, x 0 q = 0) :
    ∃ y : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → y p q = 0) ∧ (∀ q, y 0 q = 0) ∧ K.D y = x := by
  cases n with
  | zero =>
    have hx0 : x = 0 := by
      funext p q
      rcases p with _ | p
      · exact h0 q
      · exact hx (p + 1) q (by omega)
    exact ⟨0, fun _ _ _ => rfl, fun _ => rfl, by rw [map_zero, hx0]⟩
  | succ m =>
    obtain ⟨z, hz, hDz⟩ := vanish (shC K) a m h.sh (by omega) (sh K x) (fun p q hpq => hx (p + 1) q (by omega))
      (by rw [D_sh K x h0, hD]; rfl)
    refine ⟨un K z, fun p q hpq => ?_, fun q => rfl, ?_⟩
    · rcases p with _ | p
      · rfl
      · exact hz p q (by omega)
    · rw [D_un, hDz, un_sh K x h0]

variable {K : DCx.{w} R} {A : Cx.{w'} R}

theorem deg_inj (e : DCx.AugRow A K) (a : ℕ) (hb : Function.Injective (e.edge.mapH a)) (h : Ex K a)
    (c : A.X a) (hc : A.d a c = 0) (hB : e.ε a c ∈ (K.col 0).B a) : c ∈ A.B a := by
  have hz : K.tot.d a (e.edge.f a c) = 0 := by rw [e.edge.comm, hc, map_zero]
  have key : e.edge.f a c ∈ K.tot.B a := by
    cases a with
    | zero =>
      have h0 : e.ε 0 c = 0 := (Submodule.mem_bot R).1 hB
      change (K.inj 0 0 0 (Nat.zero_add 0)) (e.ε 0 c) ∈ _
      rw [h0, map_zero]
      exact Submodule.zero_mem _
    | succ m =>
      obtain ⟨w, hw⟩ := hB
      have hw' : K.dv 0 m w = e.ε (m + 1) c := hw
      have hsT : K.sgl 0 m w ∈ K.T m := fun p q hpq => K.sgl_ne w (by omega)
      set x := (e.edge.f (m + 1) c).1 - K.D (K.sgl 0 m w) with hxdef
      have hxT : x ∈ K.T (m + 1) := Submodule.sub_mem _ (e.edge.f (m + 1) c).2 (K.D_mem m _ hsT)
      have hDx : K.D x = 0 := by
        rw [hxdef, map_sub, K.DD, sub_zero]
        exact congrArg Subtype.val hz
      have h0 : ∀ q, x 0 q = 0 := by
        intro q
        rw [hxdef, K.D_sgl, hw']
        change K.sgl 0 (m + 1) (e.ε (m + 1) c) 0 q - _ = 0
        simp only [pow_zero, one_smul, Pi.add_apply, Pi.sub_apply]
        rw [K.sgl_ne (K.dh 0 m w) (Or.inl (by omega) : 0 ≠ 0 + 1 ∨ q ≠ m)]
        simp
      obtain ⟨y, hy, -, hDy⟩ := tail K (m + 1) (m + 1) h le_rfl x hxT hDx h0
      have hyT : K.sgl 0 m w + y ∈ K.T m :=
        Submodule.add_mem _ hsT fun p q hpq => hy p q (by omega)
      refine ⟨⟨_, hyT⟩, Subtype.ext ?_⟩
      change K.D (K.sgl 0 m w + y) = (e.edge.f (m + 1) c).1
      rw [map_add, hDy, hxdef]
      abel
  have h1 : e.edge.mapH a (A.cls c hc) = 0 := by
    rw [P.mapH_cls _ a c hc hz]
    exact ((P.cls_surj K.tot a).2.1 _ hz).2 key
  exact ((P.cls_surj A a).2.1 c hc).1 (hb (h1.trans (map_zero _).symm))

theorem extend (a : ℕ) (h : Ex K a) (y₀ : K.X 0 a) (hy : K.dv 0 a y₀ = 0) (hB : K.dh 0 a y₀ ∈ (K.col 1).B a) :
    ∃ x : ∀ p q, K.X p q, x ∈ K.T a ∧ K.D x = 0 ∧ x 0 a = y₀ := by
  cases a with
  | zero =>
    have h0 : K.dh 0 0 y₀ = 0 := (Submodule.mem_bot R).1 hB
    refine ⟨K.sgl 0 0 y₀, fun p q hpq => K.sgl_ne _ (by omega), ?_, K.sgl_self _ _ _⟩
    rw [K.D_sgl, h0, hy]
    simp
  | succ m =>
    obtain ⟨z, hz⟩ := hB
    have hz' : K.dv 1 m z = K.dh 0 (m + 1) y₀ := hz
    set x₁ := K.sgl 0 (m + 1) y₀ + K.sgl 1 m z with hx₁
    set c := K.sgl 2 m (K.dh 1 m z) with hc
    have hDx₁ : K.D x₁ = c := by
      rw [hx₁, map_add, K.D_sgl, K.D_sgl, hy, hz']
      simp [hc]
    have hc0 : ∀ q, c 0 q = 0 := fun q => K.sgl_ne _ (Or.inl (by omega))
    have hc1 : ∀ q, c 1 q = 0 := fun q => K.sgl_ne _ (Or.inl (by omega))
    have hDc : K.D c = 0 := by rw [← hDx₁, K.DD]
    obtain ⟨y', hy1, hy2, hy3⟩ := tail (shC K) (m + 1) (m + 1) h.sh le_rfl (sh K c)
      (fun p q hpq => K.sgl_ne _ (by omega)) (by rw [D_sh K c hc0, hDc]; rfl) hc1
    refine ⟨x₁ - un K y', fun p q hpq => ?_, ?_, ?_⟩
    · have h1 : x₁ p q = 0 := by
        rw [hx₁, Pi.add_apply, Pi.add_apply, K.sgl_ne _ (by omega), K.sgl_ne _ (by omega), add_zero]
      have h2 : un K y' p q = 0 := by
        rcases p with _ | p
        · rfl
        · exact hy1 p q (by omega)
      rw [Pi.sub_apply, Pi.sub_apply, h1, h2, sub_zero]
    · rw [map_sub, D_un, hy3, un_sh K c hc0, hDx₁, sub_self]
    · change x₁ 0 (m + 1) - 0 = y₀
      rw [sub_zero, hx₁, Pi.add_apply, Pi.add_apply, K.sgl_self, K.sgl_ne _ (Or.inl (by omega)), add_zero]

theorem deg_surj (e : DCx.AugRow A K) (a : ℕ) (hb : Function.Surjective (e.edge.mapH a)) (h : Ex K a)
    (y₀ : K.X 0 a) (hy : K.dv 0 a y₀ = 0) (hB : K.dh 0 a y₀ ∈ (K.col 1).B a) :
    ∃ (c : A.X a) (_ : A.d a c = 0), e.ε a c - y₀ ∈ (K.col 0).B a := by
  obtain ⟨x, hxT, hDx, hx0⟩ := extend a h y₀ hy hB
  have hxc : K.tot.d a ⟨x, hxT⟩ = 0 := Subtype.ext hDx
  obtain ⟨t, ht⟩ := hb (K.tot.cls ⟨x, hxT⟩ hxc)
  obtain ⟨c, hc, rfl⟩ := (P.cls_surj A a).1 t
  have hz : K.tot.d a (e.edge.f a c) = 0 := by rw [e.edge.comm, hc, map_zero]
  rw [P.mapH_cls _ a c hc hz] at ht
  have hd := ((P.cls_surj K.tot a).2.2.1 _ _ hz hxc).1 ht
  refine ⟨c, hc, ?_⟩
  have hv : (e.edge.f a c).1 0 a = e.ε a c := K.sgl_self _ _ _
  cases a with
  | zero =>
    have h0 := congrArg Subtype.val ((Submodule.mem_bot R).1 hd)
    have h1 : (e.edge.f 0 c).1 0 0 - x 0 0 = 0 := congrFun (congrFun h0 0) 0
    rw [hv, hx0] at h1
    rw [h1]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨w, hw⟩ := hd
    have h1 : K.D w.1 0 (m + 1) = (e.edge.f (m + 1) c).1 0 (m + 1) - x 0 (m + 1) :=
      congrFun (congrFun (congrArg Subtype.val hw) 0) (m + 1)
    rw [hv, hx0] at h1
    refine ⟨w.1 0 m, ?_⟩
    rw [← h1]
    simp [DCx.D_apply, DCx.Dh, DCx.Dv]

end Abstract

section Cover

universe u v

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

def prj (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (p : ℕ) (i : Fin (p + 1) → ι) :
    Cx.Hom ((cechCC F U).dcx.col p) (CH.cx ((capT U i).ι ⋙ F)) (RingHom.id R) :=
  ⟨fun _ => LinearMap.proj i, fun _ _ => rfl⟩

theorem prj_bij (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (p q : ℕ) :
    Function.Bijective (fun (x : ((cechCC F U).dcx.col p).H q) i => (prj F U p i).mapH q x) :=
  GlobalTheory.CompanionTheory.CechSerre.pi_H_bij (fun i : Fin (p + 1) → ι => CH.cx ((capT U i).ι ⋙ F)) (prj F U p)
    (fun _ => Function.bijective_id) q

theorem ex_of (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (a : ℕ)
    (hvan : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : ℕ), j < a → Subsingleton (HU F (capT U i) j)) :
    Ex (cechCC F U).dcx a := by
  intro p
  refine ⟨fun ha => ?_, fun q hq x hx => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    funext i
    have hzi : CH.d ((capT U i).ι ⋙ F) 0 (z i) = 0 := congrFun hz i
    have := hvan p i 0 ha
    have h0 : (CH.cx ((capT U i).ι ⋙ F)).cls (z i) hzi = 0 := Subsingleton.elim _ _
    exact (Submodule.mem_bot R).1 (((P.cls_surj _ 0).2.1 _ hzi).1 h0)
  · have hex : ∀ i, ∃ y, CH.d ((capT U i).ι ⋙ F) q y = x i := by
      intro i
      have hxi : CH.d ((capT U i).ι ⋙ F) (q + 1) (x i) = 0 := congrFun hx i
      have := hvan p i (q + 1) hq
      have h0 : (CH.cx ((capT U i).ι ⋙ F)).cls (x i) hxi = 0 := Subsingleton.elim _ _
      exact ((P.cls_surj _ (q + 1)).2.1 _ hxi).1 h0
    choose y hy using hex
    exact ⟨y, funext hy⟩

theorem edge_bij (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) : Function.Bijective ((cechAugRowU F U).edge.mapH n) := by
  have := P.dc_row (cechAugRowU F U) 1 (GlobalTheory.CompanionTheory.CechRowExact.cech_rows F U hU hc) n
  rw [one_pow] at this
  exact (P.upTo_alg _ (LinearMap.id (R := R)) 1 1).2.2.2.2.1 this

theorem prj_eps (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (a : ℕ) (i : Fin (0 + 1) → ι)
    (c : CH.Cn F a) (hc : CH.d F a c = 0) (hε : ((cechCC F U).dcx.col 0).d a ((cechAugRowU F U).ε a c) = 0) :
    (prj F U 0 i).mapH a (((cechCC F U).dcx.col 0).cls _ hε) =
      (CH.Mor.restrict F (capT U i).ι).pull a ((CH.cx F).cls c hc) := rfl

theorem cov_inj (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hvan : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : ℕ), j < a → Subsingleton (HU F (capT U i) j))
    (x : CH.H F a) (hx : ∀ i : Fin (0 + 1) → ι, (CH.Mor.restrict F (capT U i).ι).pull a x = 0) : x = 0 := by
  obtain ⟨c, hcz, rfl⟩ := (P.cls_surj (CH.cx F) a).1 x
  have hε : ((cechCC F U).dcx.col 0).d a ((cechAugRowU F U).ε a c) = 0 := by
    refine ((cechAugRowU F U).comm a c).trans ?_
    rw [show (CH.cx F).d a c = 0 from hcz, map_zero]
  have h1 : ((cechCC F U).dcx.col 0).cls _ hε = 0 := (prj_bij F U 0 a).1 (funext fun i => by
    simp only [map_zero]
    exact (prj_eps F U a i c hcz hε).trans (hx i))
  have hB := ((P.cls_surj _ a).2.1 _ hε).1 h1
  exact ((P.cls_surj (CH.cx F) a).2.1 c hcz).2
    (deg_inj (cechAugRowU F U) a (edge_bij F U hU hc a).1 (ex_of F U a hvan) c hcz hB)

theorem cov_glue (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hvan : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : ℕ), j < a → Subsingleton (HU F (capT U i) j))
    (y : ∀ i : Fin (0 + 1) → ι, HU F (capT U i) a)
    (hy : ∀ t : Fin (1 + 1) → ι,
      (resU F (U := capT U (t ∘ (0 : Fin 2).succAbove)) (V := capT U t) fun _ h _ => h _).pull a (y (t ∘ (0 : Fin 2).succAbove)) =
      (resU F (U := capT U (t ∘ (1 : Fin 2).succAbove)) (V := capT U t) fun _ h _ => h _).pull a (y (t ∘ (1 : Fin 2).succAbove))) :
    ∃ x : CH.H F a, ∀ i, (CH.Mor.restrict F (capT U i).ι).pull a x = y i := by
  obtain ⟨ŷ, hŷ⟩ := (prj_bij F U 0 a).2 y
  obtain ⟨y₀, hy₀, rfl⟩ := (P.cls_surj _ a).1 ŷ
  have hzi : ∀ i : Fin (0 + 1) → ι, CH.d ((capT U i).ι ⋙ F) a (y₀ i) = 0 := fun i => congrFun hy₀ i
  have hyi : ∀ i : Fin (0 + 1) → ι, y i = (CH.cx ((capT U i).ι ⋙ F)).cls (y₀ i) (hzi i) := fun i =>
    (congrFun hŷ i).symm
  have hdz : ((cechCC F U).dcx.col 1).d a ((cechCC F U).dcx.dh 0 a y₀) = 0 := by
    refine ((cechCC F U).dcx.hv 0 a y₀).symm.trans ?_
    rw [show (cechCC F U).dcx.dv 0 a y₀ = 0 from hy₀, map_zero]
  have hcl : ((cechCC F U).dcx.col 1).cls _ hdz = 0 := (prj_bij F U 1 a).1 (funext fun t => by
    simp only [map_zero]
    have hval : (cechCC F U).dcx.dh 0 a y₀ t =
        (resU F (U := capT U (t ∘ (0 : Fin 2).succAbove)) (V := capT U t) fun _ h _ => h _).pullC a (y₀ (t ∘ (0 : Fin 2).succAbove)) -
        (resU F (U := capT U (t ∘ (1 : Fin 2).succAbove)) (V := capT U t) fun _ h _ => h _).pullC a (y₀ (t ∘ (1 : Fin 2).succAbove)) := by
      have e := congrFun (Cos.d_apply ((cechCC F U).cos a) 0 y₀) t
      rw [Fin.sum_univ_two] at e
      refine e.trans ?_
      simp [sub_eq_add_neg]
    have h0 := hy t
    rw [hyi, hyi] at h0
    have h1 := ((P.cls_surj (CH.cx ((capT U t).ι ⋙ F)) a).2.2.1 _ _
      (((resU F _).d_pullC a _).trans (by rw [hzi, map_zero]))
      (((resU F _).d_pullC a _).trans (by rw [hzi, map_zero]))).1 h0
    rw [← hval] at h1
    exact ((P.cls_surj _ a).2.1 _ _).2 h1)
  have hB := ((P.cls_surj _ a).2.1 _ hdz).1 hcl
  obtain ⟨c, hcz, hd⟩ := deg_surj (cechAugRowU F U) a (edge_bij F U hU hc a).2 (ex_of F U a hvan) y₀ hy₀ hB
  have hε : ((cechCC F U).dcx.col 0).d a ((cechAugRowU F U).ε a c) = 0 := by
    refine ((cechAugRowU F U).comm a c).trans ?_
    rw [hcz, map_zero]
  have heq := ((P.cls_surj _ a).2.2.1 _ _ hε hy₀).2 hd
  refine ⟨(CH.cx F).cls c hcz, fun i => ?_⟩
  rw [← prj_eps F U a i c hcz hε, heq]
  exact congrFun hŷ i

def kap (F : C ⥤ ModuleCat.{w} R) {P Q' : ObjectProperty C} {Q : ObjectProperty P.FullSubcategory}
    (h : ∀ T, Q T → Q' T.obj) : CH.Mor (Q'.ι ⋙ F) (Q.ι ⋙ P.ι ⋙ F) (RingHom.id R) where
  G := Q'.lift (Q.ι ⋙ P.ι) fun T => h _ T.property
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem kap_bij (F : C ⥤ ModuleCat.{w} R) {P Q' : ObjectProperty C} {Q : ObjectProperty P.FullSubcategory}
    (h : ∀ T, Q T → Q' T.obj) (h' : ∀ T, Q' T → ∃ hp : P T, Q ⟨T, hp⟩) (n : ℕ) :
    Function.Bijective ((kap F h).pull n) := by
  let L : Q'.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift (P.lift Q'.ι fun T => (h' _ T.property).choose) fun T => (h' _ T.property).choose_spec
  refine CrystallineSemistableComparison.P.mapH_bij (kap F h).hom (fun k => ⟨fun z z' e => funext fun s => ?_, fun w => ⟨fun s => w (s ⋙ L), ?_⟩⟩) n
  · exact congrFun e (s ⋙ L)
  · funext t
    rfl

theorem kap_top (F : C ⥤ ModuleCat.{w} R) {Top P Q' : ObjectProperty C} {Q : ObjectProperty P.FullSubcategory}
    (h : ∀ T, Q T → Q' T.obj) (hP : P ≤ Top) (hQ : Q' ≤ Top) (n : ℕ) (x : HU F Top n) :
    (CH.Mor.restrict (P.ι ⋙ F) Q.ι).pull n ((resU F hP).pull n x) = (kap F h).pull n ((resU F hQ).pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem kap_res (F : C ⥤ ModuleCat.{w} R) {P Q₁' Q₂' : ObjectProperty C} {Q₁ Q₂ : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, Q₁ T → Q₁' T.obj) (h₂ : ∀ T, Q₂ T → Q₂' T.obj) (hle : Q₁ ≤ Q₂) (hle' : Q₁' ≤ Q₂') (n : ℕ)
    (x : HU F Q₂' n) :
    (resU (P.ι ⋙ F) hle).pull n ((kap F h₂).pull n x) = (kap F h₁).pull n ((resU F hle').pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem descent (F : C ⥤ ModuleCat.{w} R) {ι : Type} (Top : ObjectProperty C) (V : ι → ObjectProperty C)
    (W : ι → ι → ObjectProperty C) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α β T, W α β T ↔ V α T ∧ V β T)
    (hcov : (fun T => ∃ α, V α T) ≤ Top) (a : ℕ)
    (hb : ∀ n, Function.Bijective ((resU F hcov).pull n))
    (hvan : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : ℕ), j < a → Subsingleton (HU F (capT V i) j))
    (h : ∀ α, V α ≤ Top) (h₁ : ∀ α β, W α β ≤ V α) (h₂ : ∀ α β, W α β ≤ V β) :
    Function.Injective (fun (x : HU F Top a) α => (resU F (h α)).pull a x) ∧
    ∀ y : ∀ α, HU F (V α) a, (∀ α β, (resU F (h₁ α β)).pull a (y α) = (resU F (h₂ α β)).pull a (y β)) →
      ∃ x, ∀ α, (resU F (h α)).pull a x = y α := by
  let cov : ObjectProperty C := fun T => ∃ α, V α T
  let U' : ι → ObjectProperty cov.FullSubcategory := fun α T => V α T.obj
  have hU' : ∀ α, Cosieve (U' α) := fun α T T' φ hT => hV α φ.hom hT
  have hc' : ∀ T, ∃ α, U' α T := fun T => T.property
  have hvan' : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : ℕ), j < a →
      Subsingleton (HU (cov.ι ⋙ F) (capT U' i) j) := by
    intro p i j hj
    have := hvan p i j hj
    exact (kap_bij F (P := cov) (Q := capT U' i) (Q' := capT V i) (fun T hT => hT)
      (fun T hT => ⟨⟨i 0, hT 0⟩, hT⟩) j).2.subsingleton
  have k1 : ∀ (i : Fin (0 + 1) → ι) (T : cov.FullSubcategory), capT U' i T → V (i 0) T.obj := fun i T hT => hT 0
  have k1' : ∀ (i : Fin (0 + 1) → ι) (T : C), V (i 0) T → ∃ hp : cov T, capT U' i ⟨T, hp⟩ := fun i T hT =>
    ⟨⟨i 0, hT⟩, fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hT⟩
  constructor
  · intro x x' hxx
    refine (hb a).1 (sub_eq_zero.1 ?_)
    rw [← map_sub]
    refine cov_inj (cov.ι ⋙ F) U' hU' hc' a hvan' _ fun i => ?_
    rw [kap_top F (k1 i) hcov (h (i 0)), map_sub, map_sub]
    have := congrFun hxx (i 0)
    simp only at this
    rw [this, sub_self]
  · intro y hy
    obtain ⟨x', hx'⟩ := cov_glue (cov.ι ⋙ F) U' hU' hc' a hvan' (fun i => (kap F (k1 i)).pull a (y (i 0))) (fun t => by
      have kt : ∀ (T : cov.FullSubcategory), capT U' t T → W (t 0) (t 1) T.obj := fun T hT => (hW _ _ _).2 ⟨hT 0, hT 1⟩
      refine (kap_res F kt (k1 (t ∘ (0 : Fin 2).succAbove)) _ (h₂ (t 0) (t 1)) a _).trans ?_
      refine Eq.trans ?_ (kap_res F kt (k1 (t ∘ (1 : Fin 2).succAbove)) _ (h₁ (t 0) (t 1)) a _).symm
      exact congrArg _ (hy (t 0) (t 1)).symm)
    obtain ⟨x, rfl⟩ := (hb a).2 x'
    refine ⟨x, fun α => ?_⟩
    refine (kap_bij F (k1 fun _ => α) (k1' fun _ => α) a).1 ?_
    exact (kap_top F (k1 fun _ => α) hcov (h α) a x).symm.trans (hx' fun _ => α)

end Cover

end GlobalTheory.CompanionTheory.CechDeg

theorem GlobalTheory.CompanionTheory.CechDeg.om_cech : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens),
    (⨆ α, U α) = ⊤ → ∀ a : ℕ, (∀ S : Finset ι, S.Nonempty → ∀ j < a, Subsingleton (CrystallineSemistableComparison.Onto.HV q (⨅ α ∈ S, U α) a j)) →
    ∀ (h : ∀ α, CrystallineSemistableComparison.Onto.inU q (U α) ≤ CrystallineSemistableComparison.Onto.inU q ⊤)
      (h₁ : ∀ α β, CrystallineSemistableComparison.Onto.inU q (U α ⊓ U β) ≤ CrystallineSemistableComparison.Onto.inU q (U α))
      (h₂ : ∀ α β, CrystallineSemistableComparison.Onto.inU q (U α ⊓ U β) ≤ CrystallineSemistableComparison.Onto.inU q (U β)),
    Function.Injective (fun (x : CrystallineSemistableComparison.Onto.HV q ⊤ a a) α => (CrystallineSemistableComparison.Pb.resU (CrystallineSemistableComparison.Onto.G q a) (h α)).pull a x) ∧
    ∀ y : ∀ α, CrystallineSemistableComparison.Onto.HV q (U α) a a,
      (∀ α β, (CrystallineSemistableComparison.Pb.resU (CrystallineSemistableComparison.Onto.G q a) (h₁ α β)).pull a (y α) = (CrystallineSemistableComparison.Pb.resU (CrystallineSemistableComparison.Onto.G q a) (h₂ α β)).pull a (y β)) →
      ∃ x, ∀ α, (CrystallineSemistableComparison.Pb.resU (CrystallineSemistableComparison.Onto.G q a) (h α)).pull a x = y α := by
  intro K _ X q ι U hU a hvan h h₁ h₂
  classical
  have hcov : (fun T => ∃ α, CrystallineSemistableComparison.Onto.inU q (U α) T) ≤ CrystallineSemistableComparison.Onto.inU q ⊤ := fun T ⟨α, hα⟩ => h α T hα
  refine GlobalTheory.CompanionTheory.CechDeg.descent (CrystallineSemistableComparison.Onto.G q a) (CrystallineSemistableComparison.Onto.inU q ⊤) (fun α => CrystallineSemistableComparison.Onto.inU q (U α))
    (fun α β => CrystallineSemistableComparison.Onto.inU q (U α ⊓ U β)) (fun α T T' φ hT => GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ hT)
    (fun α β T => ⟨fun hT => ⟨fun _ hx => (hT hx).1, fun _ hx => (hT hx).2⟩, fun hT _ hx => ⟨hT.1 hx, hT.2 hx⟩⟩)
    hcov a (fun n => CrystallineSemistableComparison.Onto.zarAbs_pf K X q ι ⊤ U hU hcov a n) ?_ h h₁ h₂
  intro p i j hj
  have hS : (Finset.univ.image i).Nonempty := ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have := hvan _ hS j hj
  have e₁ : CrystallineSemistableComparison.Pb.capT (fun α => CrystallineSemistableComparison.Onto.inU q (U α)) i ≤ CrystallineSemistableComparison.Onto.inU q (⨅ α ∈ Finset.univ.image i, U α) :=
    fun T hT => (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U _ T).2 fun α hα => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
      exact hT k
  have e₂ : CrystallineSemistableComparison.Onto.inU q (⨅ α ∈ Finset.univ.image i, U α) ≤ CrystallineSemistableComparison.Pb.capT (fun α => CrystallineSemistableComparison.Onto.inU q (U α)) i :=
    fun T hT k => (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U _ T).1 hT _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  exact (CrystallineSemistableComparison.Onto.resU_bij_of_le (CrystallineSemistableComparison.Onto.G q a) e₁ e₂ j).2.subsingleton

end
