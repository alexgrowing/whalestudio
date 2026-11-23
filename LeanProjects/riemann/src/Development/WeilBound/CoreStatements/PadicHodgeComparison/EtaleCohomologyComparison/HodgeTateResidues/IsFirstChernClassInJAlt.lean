import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option genSizeOf false
set_option genInjectivity false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

universe v u

namespace CrystallineSemistableComparison.HT

open PAlg Pb

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {Φ : PDF R C}

def idS (Φ : PDF R C) : SMor Φ Φ (RingHom.id R) where
  G := 𝟭 C
  ρ _ := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end Gen

theorem dividedPowerFiltration_red {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {B' : Type} [CommRing B'] (f : B →+* B')
    (hf : Function.Surjective f) (δ' : DividedPowers (J.map f)) (h : IsDPMorphism δ δ' f) (r : ℕ) : pdP δ' r ≤ (pdP δ r).map f := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B'), (∀ q ∈ l, q.2 ∈ J.map f) → ∃ l' : List (ℕ × B), (∀ q ∈ l', q.2 ∈ J) ∧
      l'.map Prod.fst = l.map Prod.fst ∧ f (l'.map fun q => δ.dpow q.1 q.2).prod = (l.map fun q => δ'.dpow q.1 q.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], by simp, rfl, by simp⟩
    | cons q l ih =>
      intro hl
      obtain ⟨l', h1, h2, h3⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ hf).1 (hl q List.mem_cons_self)
      refine ⟨(q.1, y) :: l', ?_, by simp [h2], ?_⟩
      · intro q' hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        exacts [hy, h1 q' hq']
      · simp only [List.map_cons, List.prod_cons, map_mul, h3]
        rw [← e, h.2 y hy]
  obtain ⟨l', h1, h2, h3⟩ := key l hl
  rw [← h3]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨l', h1, h2 ▸ hr, rfl⟩)

section Base
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem fil_mul_le {t : b.R} (ht : t ∈ b.I) {k r r' : ℕ} (h : r' ≤ r + k) (T : Thick L) {x : T.B} (hx : x ∈ T.pdPow r) :
    T.i (t ^ k) * x ∈ T.pdPow r' := by
  rw [map_pow]
  exact T.pdPow_anti h (dividedPowerFiltration_pow_mul T.δ (T.i_mem ht) rfl hx)

theorem grOkQ {a a' c : ℕ} (h : a + a' = c) :
    MulOk (sFil Q a) (sFil Q ((a : ℤ) + 1)) (sFil Q a') (sFil Q ((a' : ℤ) + 1)) (sFil Q c) (sFil Q ((c : ℤ) + 1)) :=
  ⟨fun T _ _ => (grOk L h).aa T.obj, fun T _ _ => (grOk L h).ab T.obj, fun T _ _ => (grOk L h).ba T.obj⟩

abbrev HG (r j : ℕ) : Type 1 := HQ Q (r : ℤ) ((r : ℤ) + 1) j

def cupG {r r' s i j : ℕ} (h : r + r' = s) (x : HG Q r i) (y : HG Q r' j) : HG Q s (i + j) := (grOkQ Q h).pair.cup rfl x y

def shG {t : b.R} (ht : t ∈ b.I) {r r' : ℕ} (k : ℕ) (h : r + k = r') (j : ℕ) : HG Q r j →ₗ[b.R] HG Q r' j :=
  ((idS (sP Q)).sqC (t ^ k) (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := sFil Q r') (b' := sFil Q ((r' : ℤ) + 1))
    (fun T _ hx => fil_mul_le ht (r := r) (r' := r') (by omega) T.obj hx)
    fun T _ hx => fil_mul_le ht (r := r + 1) (r' := r' + 1) (by omega) T.obj hx).pull j

abbrev HGm (c : b.R) (r j : ℕ) : Type 1 := CH.H (sq (stdI Q (some (r : ℤ)) c) (stdI Q (some ((r : ℤ) + 1)) c)) j

def redG' (c : b.R) (r j : ℕ) : HG Q r j →ₗ[b.R] HGm Q c r j :=
  (sqLe (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := stdI Q (some (r : ℤ)) c) (b' := stdI Q (some ((r : ℤ) + 1)) c)
    (fun _ => le_sup_left) fun _ => le_sup_left).pull j

def trG (c : b.R) (n r j : ℕ) : HGm Q (c ^ (n + 1)) r j →ₗ[b.R] HGm Q (c ^ n) r j :=
  (sqLe (stdI_le Q (some (r : ℤ)) c n) (stdI_le Q (some ((r : ℤ) + 1)) c n)).pull j

end Base

section Rat
variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K)) (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I))))

def kS : SMor (thP (smFun X q)) (sP Q) (algebraMap K B) where
  G := Q.ι ⋙ ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

def muG {t : B} (ht : t ∈ I) (a r j : ℕ) : Hdg q a j →ₛₗ[algebraMap K B] HG Q r j :=
  ((kS γ q Q).sqC (t ^ (r - a)) (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := sFil Q r) (b' := sFil Q ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a) (r' := r) (by omega) T.obj hx)
    fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx).pull j

variable {E : Type} [CommRing E] (θ : B →+* E)

structure IsCo {t : B} (ht : t ∈ I) (r j : ℕ) (co : HG Q r j →+ ∀ a, Module.Dual K (Hdg q a j) →+ E) : Prop where
  smul : ∀ (b : B) w a φ, co (b • w) a φ = θ b * co w a φ
  lin : ∀ w a (k : K) φ, co w a (k • φ) = θ (algebraMap K B k) * co w a φ
  same : ∀ a ≤ r, ∀ y φ, co (muG γ q Q ht a r j y) a φ = θ (algebraMap K B (φ y))
  diff : ∀ a a', a ≠ a' → ∀ y, co (muG γ q Q ht a' r j y) a = 0
  big : ∀ a, r < a → ∀ w, co w a = 0

def Spans {t : B} (ht : t ∈ I) (r j : ℕ) : Prop :=
  Submodule.span B {w : HG Q r j | ∃ a ≤ r, ∃ y, w = muG γ q Q ht a r j y} = ⊤

end Rat

section Red
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
  {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {l n : ℕ}
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (d : RedIn γ' κ' γ l n)
  {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem red_mem (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : T.obj.B ⧸ lnT T.obj l n) (hx : x ∈ pdP (redδ T.obj T.property.1 n) r) :
    Ideal.Quotient.factor (ln_le q s 𝒱 (some ((r : ℤ) + 1)) T) x ∈
      ((stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)).S T).map (Ideal.Quotient.mk _) := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (dividedPowerFiltration_red T.obj.δ _ Ideal.Quotient.mk_surjective _ (redδ_dp T.obj T.property.1 n) r hx)
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk _) (Ideal.mem_sup_left hy)

def redSub (r : ℕ) : CH.Mor (B.pdS (nlFun γ' l X q κ') c r).fn
    (sq (stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (stdI (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) ((l : A) ^ n))) lam where
  G := redG q s d 𝒱
  τ T :=
    { toFun := fun x => ⟨((redMor q s d 𝒱 c lam hc (some ((r : ℤ) + 1))).τ T (Subtype.val x)).1,
        red_mem q s 𝒱 r T (Subtype.val x) ((mem_pdS (T := redObj T.obj d T.property.1)).1 (Subtype.property x))⟩
      map_add' := fun x y => by
        have h := congrArg Subtype.val (map_add ((redMor q s d 𝒱 c lam hc (some ((r : ℤ) + 1))).τ T) (Subtype.val x) (Subtype.val y))
        exact Subtype.ext h
      map_smul' := fun a x => by
        have h := congrArg Subtype.val
          (LinearMap.map_smulₛₗ ((redMor q s d 𝒱 c lam hc (some ((r : ℤ) + 1))).τ T) a (Subtype.val x))
        exact Subtype.ext h }
  nat φ x := by
    have h := congrArg Subtype.val ((redMor q s d 𝒱 c lam hc (some ((r : ℤ) + 1))).nat φ (Subtype.val x))
    exact Subtype.ext h

end Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l K) in

structure CB : Type 1 where
  Λ : Type
  [ring : CommRing Λ]
  R : ℕ → Type
  [ringR : ∀ n, CommRing (R n)]
  I : ∀ n, Ideal (R n)
  γ : ∀ n, DividedPowers (I n)
  κ : ∀ n, OK l K →+* R n ⧸ I n
  c : ∀ n, Λ →+* R n
  c_surj : ∀ n, Function.Surjective (c n)
  t : Λ
  ht : ∀ n, c n t ∈ I n
  θ : Λ →+* ℂ_[l]
  rd : ∀ n, R (n + 1) →+* R n
  rd_dp : ∀ n, IsDPMorphism (γ (n + 1)) (γ n) (rd n)
  rd_κ : ∀ n, (Ideal.quotientMap _ (rd n) (Ideal.map_le_iff_le_comap.1 (rd_dp n).1)).comp (κ (n + 1)) = κ n
  rd_c : ∀ n a, rd n (c (n + 1) a) = c n a

attribute [instance] CB.ring CB.ringR

namespace CB

variable (Y : CB l K)

abbrev bs (n : ℕ) : Base := nlBase (Y.R n) (Y.I n) (Y.γ n) l

abbrev L (M : Model l K) (n : ℕ) : (Y.bs n).Fun := (B.schFn M.p).cr (Y.bs n) rfl (Y.κ n)

abbrev SS (M : Model l K) (r n : ℕ) : CH.SubF (B.OM (Y.L M n) (Y.c n)) := B.pdS (Y.L M n) (Y.c n) r

def Fam (M : Model l K) (r j : ℕ) : Type 1 := ∀ n, CH.H (Y.SS M r n).fn j

instance (M : Model l K) (r j : ℕ) : AddCommGroup (Y.Fam M r j) := Pi.addCommGroup
instance (M : Model l K) (r j : ℕ) : Module Y.Λ (Y.Fam M r j) := Pi.module _ _ _

def redM (M : Model l K) (n : ℕ) : GlobalTheory.LogCris.Mor (Y.L M (n + 1)) (Y.L M n) (Y.rd n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Y.bs (n + 1)) (b' := Y.bs n) (ht := rfl) (ht' := rfl) (Y.rd n) rfl
    (Y.rd_dp n) (B.basePt _ _ (Y.rd_κ n)) fun _ _ _ => rfl

variable {Y} {M : Model l K}

def Comp {r j : ℕ} (x : Y.Fam M r j) : Prop := ∀ n, (pdOm (Y.redM M n) (RingHom.id _) (Y.rd_c n) r).pull j (x (n + 1)) = x n

def cupS {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) : Y.Fam M s (i + j) := fun n =>
  (pdPair (Y.L M n) (Y.c n) h).cup rfl (x n) (y n)

variable (Y M) in

def oneS : Y.Fam M 0 0 := fun n => pdOne (Y.L M n) (Y.c n)

def shS {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) : Y.Fam M r' j := fun n =>
  (pdSh (Y.L M n) (Y.c n) (Y.ht n) k h).pull j (x n)

def IsFirstChernClassInFamily (D : E.LineData M.X) (x : Y.Fam M 1 2) : Prop :=
  ∀ (n : ℕ) (C : Type 1) [Category.{0} C] (G : C ⥤ Thick (Y.L M n))
    (Λ : B.CLift (q := M.p) (b := Y.bs n) (ht := rfl) (κ := Y.κ n) G D),
    ∃ (z : CH.Cn (G ⋙ (Y.SS M 1 n).fn) 2) (hz : CH.d _ 2 z = 0),
      (∀ s, (show (Y.SS M 1 n).S _ from z s).1 = Λ.coc (Y.c n) (l * n) s) ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (Y.SS M 1 n).fn G).pull 2 (x n)

end CB

structure Lv (Y : CB l K) (m : ℕ) where
  B : Type
  [bring : CommRing B]
  [balg : Algebra K B]
  IB : Ideal B
  γB : DividedPowers IB
  θ : B →+* ℂ_[l]
  A : Type
  [aring : CommRing A]
  [aalg : Algebra (OK l K) A]
  I : Ideal A
  γ : DividedPowers I
  ι : A →+* B
  lam : Y.Λ →+* A
  d : ∀ n, RedIn (O := OK l K) (Y.γ n) (Y.κ n) γ l n
  d_lam : ∀ n c, (d n).ρ (Y.c n c) = Ideal.Quotient.mk _ (lam c)
  lat : LatBase γ l m
  ι_dp : IsDPMorphism γ γB ι
  ι_O : ∀ a : OK l K, ι (algebraMap (OK l K) A a) = algebraMap K B (a : K)
  t_mem : lam Y.t ∈ I
  θ_K : ∀ k : K, θ (algebraMap K B k) = kC K k
  θ_lam : ∀ c, θ (ι (lam c)) = Y.θ c
  ker_θ : RingHom.ker θ = IB
  pdB : ∀ r, pdP γB r = Ideal.span {ι (lam Y.t) ^ r}
  nil : ι (lam Y.t) ^ m = 0
  gr : ∀ i < m, ∀ x : B, x * ι (lam Y.t) ^ i ∈ Ideal.span {ι (lam Y.t) ^ (i + 1)} → x ∈ IB

attribute [instance] Lv.bring Lv.balg Lv.aring Lv.aalg

namespace Lv

variable {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

abbrev tB : L.B := L.ι (L.lam Y.t)

theorem tB_mem : L.tB ∈ L.IB := L.ι_dp.1 (Ideal.mem_map_of_mem _ L.t_mem)

abbrev QA : ObjectProperty (Thick (nlFun L.γ 0 M.X M.p (κA (OK l K) L.I))) := TS L.γ M.p l m {⊤}

abbrev QB : ObjectProperty (Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) := TS L.γB M.q 1 m {⊤}

def rS (r n : ℕ) : CH.Mor (Y.SS M r n).fn
    (sq (stdI (L.QA M) (some (r : ℤ)) ((l : L.A) ^ n)) (stdI (L.QA M) (some ((r : ℤ) + 1)) ((l : L.A) ^ n))) L.lam :=
  redSub M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) r

def nmB : NMor L.γ M.p (κA (OK l K) L.I) L.γB M.q (κA K L.IB) L.ι where
  hI := L.ι_dp
  u := pullback.fst _ _
  g := (OK l K).subtype
  hu := pullback.condition
  hκ a r h := by
    have h1 := L.ι_dp.1 (Ideal.mem_map_of_mem L.ι (Ideal.Quotient.eq.1 h))
    rw [map_sub, L.ι_O] at h1
    exact Ideal.Quotient.eq.2 h1

theorem nmB_mem (T : Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) (h : L.QB M T) : L.QA M (((L.nmB M).mor 0).obj T) := by
  refine ⟨⟨h.1.1, fun r x hx => ?_⟩, ⊤, rfl, le_rfl⟩
  have hu : IsUnit (l : T.B) := by
    have := ((isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) : IsUnit (l : K)).map (algebraMap K L.B)).map T.i
    rwa [map_natCast, map_natCast] at this
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 hx

def bG (r j : ℕ) : HG (L.QA M) r j →ₛₗ[L.ι] HG (L.QB M) r j :=
  (((L.nmB M).smor _ _ (L.nmB_mem M)).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r) (b' := sFil _ ((r : ℤ) + 1))
    (fun _ _ hx => hx) fun _ _ hx => hx).pull j

abbrev μ (a r j : ℕ) : Hdg M.q a j →ₛₗ[algebraMap K L.B] HG (L.QB M) r j := muG L.γB M.q (L.QB M) L.tB_mem a r j

variable {M}

def Lifts {r j : ℕ} (e : ℕ) (z : HG (L.QA M) r j) (x : Y.Fam M r j) : Prop :=
  ∀ n, redG' (L.QA M) ((l : L.A) ^ n) r j z = (l : L.A) ^ e • (L.rS M r n).pull j (x n)

def Rho {r j : ℕ} (x : Y.Fam M r j) (w : HG (L.QB M) r j) : Prop := ∃ e z, L.Lifts e z x ∧ (l : L.B) ^ e • w = L.bG M r j z

end Lv

structure LHom {Y : CB l K} {m m' : ℕ} (L : Lv Y m) (L' : Lv Y m') (sΛ : Y.Λ →+* Y.Λ)
    (sn : ∀ n, Y.R n →+* Y.R n) (sC : ℂ_[l] →+* ℂ_[l]) (c : ℂ_[l]) where
  le : m' ≤ m
  sA : L.A →+* L'.A
  sB : L.B →+* L'.B
  dpA : IsDPMorphism L.γ L'.γ sA
  dpB : IsDPMorphism L.γB L'.γB sB
  oA : ∀ a : OK l K, sA (algebraMap _ _ a) = algebraMap _ _ a
  oB : ∀ k : K, sB (algebraMap _ _ k) = algebraMap _ _ k
  ι : ∀ a, sB (L.ι a) = L'.ι (sA a)
  lam : ∀ x, sA (L.lam x) = L'.lam (sΛ x)
  cris : ∀ n x, sn n (Y.c n x) = Y.c n (sΛ x)
  θ : ∀ b, L'.θ (sB b) = sC (L.θ b)
  cB : L'.B
  t : sB L.tB = cB * L'.tB
  θc : L'.θ cB = c

namespace LHom
variable {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n}
  {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def nmW : NMor L.γB N.q (κA K L.IB) L'.γB M.q (κA K L'.IB) h.sB where
  hI := h.dpB
  u := Model.genMap u hu
  g := RingHom.id K
  hu := by simpa using Model.genMap_q u hu
  hκ a r e := by
    have h1 := h.dpB.1 (Ideal.mem_map_of_mem h.sB (Ideal.Quotient.eq.1 e))
    rw [map_sub, h.oB] at h1
    exact Ideal.Quotient.eq.2 h1

theorem nmW_mem (T : Thick (nlFun L'.γB 0 M.gen M.q (κA K L'.IB))) (hT : L'.QB M T) : L.QB N (((h.nmW u hu).mor 0).obj T) :=
  ⟨⟨le_bot_iff.1 (le_trans (T.pdPow_anti h.le) hT.1.1.le), hT.1.2⟩, ⊤, rfl, le_rfl⟩

def fW (r j : ℕ) : HG (L.QB N) r j →ₛₗ[h.sB] HG (L'.QB M) r j :=
  (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r)
    (b' := sFil _ ((r : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx).pull j

end LHom

structure LvSys (Y : CB l K) {Γ : Type} (sΛ : Γ → Y.Λ →+* Y.Λ) (sn : Γ → ∀ n, Y.R n →+* Y.R n) (sC : Γ → ℂ_[l] →+* ℂ_[l])
    (c : Γ → ℂ_[l]) where
  L : ∀ m, Lv Y (m + 1)
  dn : ∀ m, LHom (L (m + 1)) (L m) (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1
  gal : ∀ (m : ℕ) (σ : Γ), LHom (L m) (L m) (sΛ σ) (sn σ) (sC σ) (c σ)

end CrystallineSemistableComparison.HT
