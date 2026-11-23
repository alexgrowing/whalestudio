import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcCov

theorem tens_transport {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    {A B : Type 1} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {S : Type} [CommRing S] {A' B' : Type 1} [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B']
    (f : Unit → N → A → A') (f' : Unit → N → B → B') (e : B →ₗ[R] A) (he : Function.Bijective e)
    (e' : B' →ₗ[S] A') (he' : Function.Bijective e') (comm : ∀ i n x, e' (f' i n x) = f i n (e x))
    (H : Tens R (N := fun _ : Unit => N) (M := fun _ => A) (M' := A') f) :
    Tens R (N := fun _ : Unit => N) (M := fun _ => B) (M' := B') f' := by
  obtain ⟨g, hg⟩ := H
  let E : B ≃ₗ[R] A := LinearEquiv.ofBijective e he
  let TE : N ⊗[R] B ≃ₗ[R] N ⊗[R] A := TensorProduct.congr (LinearEquiv.refl R N) E
  let P : (∀ _ : Unit, N ⊗[R] B) ≃+ (∀ _ : Unit, N ⊗[R] A) := AddEquiv.piCongrRight fun _ => TE.toAddEquiv
  let E' : B' ≃+ A' := (LinearEquiv.ofBijective e' he').toAddEquiv
  refine ⟨(P.trans g).trans E'.symm, fun i n x => ?_⟩
  apply E'.injective
  have hP : P (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ e x) := by
    funext k
    obtain rfl : k = i := Subsingleton.elim _ _
    simp [P, TE, E]
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hP, hg]
  exact (comm i n x).symm

section
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem pt_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (T : Thick (nlFun γ' p X q κ')) :
    pt ((m.mor p).functor.obj T) = pt T ≫ m.u := rfl

theorem inU_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (V : X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : InU V T) : InU V ((m.mor p).functor.obj T) := by
  unfold InU at h ⊢
  rw [pt_obj, hu, Category.comp_id]
  exact h

def tmor (m : NMor γ q κ γ' q κ' (algebraMap R R')) (p : ℕ) :
    SMor (thP (nlFun γ p X q κ)) (thP (nlFun γ' p X q κ')) (algebraMap R R') where
  G := (m.mor p).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end

abbrev aT {b : Base} (L : b.Fun) : IdF (thA L) := (thFil L 0).sup (IdF.span _ 0)

abbrev aB {b : Base} (L : b.Fun) : IdF (thA L) := (IdF.bot _).sup (IdF.span _ 0)

theorem aT_top {b : Base} (L : b.Fun) (T : Thick L) : (aT L).S T = ⊤ := by
  have h : (thFil L 0).S T = ⊤ := T.pdPow_zero
  exact top_le_iff.1 (h ▸ le_sup_left)

theorem aB_bot {b : Base} (L : b.Fun) (T : Thick L) : (aB L).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

theorem mapH_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K L : Cx.{1} R} {L' P : Cx.{1} R'}
    (φ : Cx.Hom K L' σ) (ψ : Cx.Hom L' P (RingHom.id R')) (φ' : Cx.Hom K L (RingHom.id R)) (ψ' : Cx.Hom L P σ) (n : ℕ)
    (h : ∀ z, ψ.f n (φ.f n z) = ψ'.f n (φ'.f n z)) (c : K.H n) : ψ.mapH n (φ.mapH n c) = ψ'.mapH n (φ'.mapH n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (h z.1))

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem leC_top (f : SMor Φ Φ' σ) (c : R') (a : IdF Φ.A) (a' : IdF Φ'.A) (h : ∀ T, a'.S T = ⊤) : f.LeC c a a' :=
  fun T _ _ => by rw [h]; trivial

theorem leC_bot (f : SMor Φ Φ' σ) (c : R') (b : IdF Φ.A) (b' : IdF Φ'.A) (h : ∀ T, b.S (f.G.obj T) = ⊥) : f.LeC c b b' := by
  intro T x hx
  rw [h, Ideal.mem_bot] at hx
  subst hx
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

theorem sqC_add (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c c' : R') (ha : f.LeC c a a') (hb : f.LeC c b b')
    (ha' : f.LeC c' a a') (hb' : f.LeC c' b b') (ha'' : f.LeC (c + c') a a') (hb'' : f.LeC (c + c') b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (c + c') ha'' hb'').τ T x = (f.sqC c ha hb).τ T x + (f.sqC c' ha' hb').τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * f.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * f.ρ T y)
  rw [map_add, add_mul, map_add]

theorem sq_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : f.Le a a') (hb : f.Le b b') (T : C')
    (v : sqM a b (f.G.obj T)) :
    (show sqM a' b' T from (f.sq ha hb).τ T v).1 = Ideal.quotientMap (b'.S T) (f.ρ T) (fun y hy => hb T y hy) v.1 := rfl

theorem sqC_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c : R') (ha : f.LeC c a a') (hb : f.LeC c b b') (T : C')
    (v : sqM a b (f.G.obj T)) : (show sqM a' b' T from (f.sqC c ha hb).τ T v).1 = f.qC c hb T v.1 := rfl

end Gen

theorem sqC_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (f : SMor Φ Φ' (algebraMap R R')) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (r : R) (c : R')
    (ha : f.LeC c a a') (hb : f.LeC c b b') (ha' : f.LeC (r • c) a a') (hb' : f.LeC (r • c) b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (r • c) ha' hb').τ T x = algebraMap R R' r • (f.sqC c ha hb).τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (r • c) * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R R' r • (algebraMap R' _ c * f.ρ T y))
  refine congrArg (Ideal.Quotient.mk _) ?_
  rw [Algebra.smul_def r c, map_mul, mul_assoc, Algebra.smul_def (algebraMap R R' r)]

section Sq
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem st_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (𝒱 : Set X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : St ⊤ 𝒱 T) : St ⊤ 𝒱 ((m.mor p).functor.obj T) := by
  obtain ⟨-, W, hW, hi⟩ := h
  exact ⟨trivial, W, hW, inU_obj m hu W T hi⟩

theorem square_tau (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (T : Q₂'.FullSubcategory) (w : (sq (oT Q₁) (oB Q₁)).obj ((m.smor Q₁ Q₁' k₁).G.obj ((incl h').G.obj T))) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).τ T (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).τ _ w) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).τ T (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).τ _ w) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine Subtype.ext ?_
  refine (sq_val (incl h') _ _ T _).trans ?_
  refine Eq.trans ?_ (sqC_val (m.smor Q₂ Q₂' k₂) a ha₂ hb₂ T _).symm
  rw [sqC_val, sq_val]
  dsimp only
  refine (congrArg (Ideal.quotientMap _ _ _) (SMor.qC_mk (m.smor Q₁ Q₁' k₁) a hb₁ ((incl h').G.obj T) y)).trans ?_
  refine (Ideal.quotientMap_mk).trans ?_
  refine Eq.trans ?_ (congrArg ((m.smor Q₂ Q₂' k₂).qC a hb₂ T) Ideal.quotientMap_mk).symm
  refine Eq.trans ?_ (SMor.qC_mk (m.smor Q₂ Q₂' k₂) a hb₂ T _).symm
  rfl

theorem pull_square (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (j : ℕ) (x : CH.H (sq (oT Q₁) (oB Q₁)) j) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).pull j (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).pull j x) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).pull j (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).pull j x) :=
  mapH_square _ _ _ _ j (fun z => funext fun s => square_tau m h h' k₁ k₂ a ha₁ hb₁ ha₂ hb₂ _ _) x

end Sq

theorem bc_cover : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  intro O R R' _ _ _ _ _ I I' γ γ' p hp hn X q κ κ' m hu hg U Q Q' hQ hQ' h ha hb j
  subst hQ hQ'
  have hA : ∀ a : R', (tmor m p).LeC a (aT _) (aT _) := fun a => leC_top _ a _ _ (aT_top _)
  have hB : ∀ a : R', (tmor m p).LeC a (aB _) (aB _) := fun a => leC_bot _ a _ _ fun T => aB_bot _ _
  have A : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oT _) (oT _) := fun 𝒱 k a => leC_top _ a _ _ fun T => aT_top _ T.obj
  have B : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oB _) (oB _) := fun 𝒱 k a => leC_bot _ a _ _ fun T => aB_bot _ _
  have Hg : Tens R (N := fun _ : Unit => R')
      (M := fun _ => CH.H (sq (oT (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      (M' := CH.H (sq (oT (St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      fun _ a x => ((m.smor _ _ (st_obj m hu _)).sqC a (A _ (st_obj m hu _) a) (B _ (st_obj m hu _) a)).pull j x := by
    refine GlobalTheory.T.stable_cover_cech_vanishing.2.2 (m.mor p).functor (fun _ : Unit => R') (fun _ => sq (aT _) (aB _)) (sq (aT _) (aB _))
      (fun _ a T => ((tmor m p).sqC a (hA a) (hB a)).τ T) (fun _ a _ _ φ x => ((tmor m p).sqC a (hA a) (hB a)).nat φ x)
      (fun _ a a' T x => sqC_add (tmor m p) a a' (hA a) (hB a) (hA a') (hB a') (hA _) (hB _) T x) (fun _ r a T x => sqC_smul (tmor m p) r a (hA a) (hB a) (hA _) (hB _) T x)
      ⊤ ⊤ U.U U.U (fun _ => st_obj m hu _) (fun _ => st_obj m hu _) (st_obj m hu _) ?_ j
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    obtain ⟨c', -⟩ := coord_res (U.c α) (iInf₂_le α hα) (U.inter S hS)
    exact GlobalTheory.CompanionTheory.ChartLocBc.local_bc hp hn m hu hg c' _ _ rfl rfl (st_obj m hu _) (A _ _) (B _ _) j
  have h₁ : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have h₂ : St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have b₁ := (zar (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₁ hc j).2.1 (some 0) none 0 0
  have b₂ := (zar (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₂ hc j).2.1 (some 0) none 0 0
  exact tens_transport _ _ _ b₁ _ b₂
    (fun _ a x => pull_square m h₁ h₂ h (st_obj m hu _) a (ha a) (hb a) (A _ _ a) (B _ _ a) j x) Hg

end GlobalTheory.CompanionTheory.BcCov
