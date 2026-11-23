import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PolAVNonzeroLocusCoverAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidGeneric

theorem exists_equiv {R K A A' V V' : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [CommRing A'] (κ : K →+* A) (κ' : K →+* A') (f : V → A) (f' : V' → A')
    (hf : Function.Injective f) (hf' : Function.Injective f')
    (lin : ∀ a b c, ∃ d, f d = f a + κ c * f b) (lin' : ∀ a b c, ∃ d, f' d = f' a + κ' c * f' b)
    (T : V' → V → Prop)
    (hl : ∀ (c : R) a' a b' b, T a' a → T b' b → ∃ d' d, T d' d ∧ f' d' = f' a' + κ' (algebraMap R K c) * f' b' ∧
      f d = f a + κ (algebraMap R K c) * f b)
    (hz : ∀ a' a, T a' a → (f' a' = 0 ↔ f a = 0))
    (he : ∀ a, ∃ c : R, c ≠ 0 ∧ ∃ b' b, T b' b ∧ f b = κ (algebraMap R K c) * f a)
    (he' : ∀ a', ∃ c : R, c ≠ 0 ∧ ∃ b' b, T b' b ∧ f' b' = κ' (algebraMap R K c) * f' a') :
    ∃ θ : V' ≃ V, (∀ a' a, θ a' = a ↔ ∃ c : R, c ≠ 0 ∧ ∃ b' b, T b' b ∧ f' b' = κ' (algebraMap R K c) * f' a' ∧
        f b = κ (algebraMap R K c) * f a) ∧
      ∀ (c : K) a b d, f' d = f' a + κ' c * f' b → f (θ d) = f (θ a) + κ c * f (θ b) := by
  let Θ : V' → V → Prop := fun a' a => ∃ c : R, c ≠ 0 ∧ ∃ b' b, T b' b ∧ f' b' = κ' (algebraMap R K c) * f' a' ∧
    f b = κ (algebraMap R K c) * f a
  have ne : ∀ {c : R}, c ≠ 0 → algebraMap R K c ≠ 0 := fun h => (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 h
  have add : ∀ (x : K) a' a b' b d' d, Θ a' a → Θ b' b → f' d' = f' a' + κ' x * f' b' → f d = f a + κ x * f b →
      Θ d' d := by
    rintro x a' a b' b d' d ⟨c₁, h₁, p', p, hp, e₁', e₁⟩ ⟨c₂, h₂, q', q, hq, e₂', e₂⟩ e' e
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hm₀ : m ≠ 0 := nonZeroDivisors.ne_zero hm
    obtain ⟨u', u, hu, eu', eu⟩ := hl (m * c₂ - 1) _ _ _ _ hp hp
    obtain ⟨v', v, hv, ev', ev⟩ := hl (n * c₁) _ _ _ _ hu hq
    have k : algebraMap R K m * (algebraMap R K n / algebraMap R K m) = algebraMap R K n :=
      mul_div_cancel₀ _ (ne hm₀)
    have k₁ := congrArg κ k
    have k₂ := congrArg κ' k
    refine ⟨m * c₁ * c₂, mul_ne_zero (mul_ne_zero hm₀ h₁) h₂, v', v, hv, ?_, ?_⟩
    · rw [ev', eu', e', e₁', e₂']
      simp only [map_mul, map_sub, map_one] at k₂ ⊢
      rw [← k₂]; ring
    · rw [ev, eu, e, e₁, e₂]
      simp only [map_mul, map_sub, map_one] at k₁ ⊢
      rw [← k₁]; ring
  have zero : ∀ a' a, Θ a' a → (f' a' = 0 ↔ f a = 0) := by
    rintro a' a ⟨c, h, p', p, hp, e', e⟩
    have := hz _ _ hp
    rwa [e', e, ((ne h).isUnit.map κ').mul_right_eq_zero, ((ne h).isUnit.map κ).mul_right_eq_zero] at this
  have uniq : ∀ a' a b' b, Θ a' a → Θ b' b → (a' = b' ↔ a = b) := fun a' a b' b ha hb => by
    obtain ⟨d', e'⟩ := lin' a' b' (-1)
    obtain ⟨d, e⟩ := lin a b (-1)
    have := zero _ _ (add _ _ _ _ _ _ _ ha hb e' e)
    rwa [e', e, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, add_neg_eq_zero, add_neg_eq_zero,
      hf.eq_iff, hf'.eq_iff] at this
  have ex' : ∀ a', ∃ a, Θ a' a := fun a' => by
    obtain ⟨c, h, p', p, hp, e⟩ := he' a'
    obtain ⟨a, ha⟩ := lin p p ((algebraMap R K c)⁻¹ - 1)
    refine ⟨a, c, h, p', p, hp, e, ?_⟩
    have k := congrArg κ (mul_inv_cancel₀ (ne h))
    rw [ha, map_sub, map_one]
    rw [map_mul, map_one] at k
    linear_combination (-f p) * k
  have ex : ∀ a, ∃ a', Θ a' a := fun a => by
    obtain ⟨c, h, p', p, hp, e⟩ := he a
    obtain ⟨a', ha⟩ := lin' p' p' ((algebraMap R K c)⁻¹ - 1)
    refine ⟨a', c, h, p', p, hp, ?_, e⟩
    have k := congrArg κ' (mul_inv_cancel₀ (ne h))
    rw [ha, map_sub, map_one]
    rw [map_mul, map_one] at k
    linear_combination (-f' p') * k
  choose t ht using ex'
  choose s hs using ex
  refine ⟨⟨t, s, fun a' => (uniq _ _ _ _ (hs _) (ht a')).2 rfl, fun a => (uniq _ _ _ _ (ht _) (hs a)).1 rfl⟩,
    fun a' a => ⟨fun h => h ▸ ht a', fun h => (uniq _ _ _ _ (ht a') h).1 rfl⟩, fun c a b d e => ?_⟩
  obtain ⟨d₁, e₁⟩ := lin (t a) (t b) c
  exact (congrArg f ((uniq _ _ _ _ (ht d) (add c _ _ _ _ _ _ (ht a) (ht b) e e₁)).1 rfl)).trans e₁

open GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR

section General

variable {X X' X'' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {k n m : ℕ}

theorem mem_ch {x : X} {j : L.ι} (h : x ∈ L.U j) : x ∈ ch L (fun _ => j) := Set.mem_iInter.2 fun _ => h

theorem fin_one (j : Fin 1 → L.ι) : j = fun _ => j 0 := funext fun a => by rw [Subsingleton.elim a 0]

abbrev sw (r : Z ⟶ X) (z : Z) (a : H0 L k) (j : L.ι) : Z.presheaf.stalk z := SecRingIso.sv r z a (fun _ => j)

def consts {R : Type} [CommRing R] (L : LB X) (p : X ⟶ Spec (CommRingCat.of R)) : R →+* (∀ j, Γ(X, ch L j)) :=
  Pi.ringHom fun j => (X.presheaf.map (homOfLE (le_top : ch L j ≤ ⊤)).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem fn_injective : Function.Injective (fn : H0 L k → _) := fun _ _ h => SecOps.sec_ext (congrFun h)

theorem exists_comb {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (a b : H0 L k) (c : R) :
    ∃ d : H0 L k, fn d = fn a + consts L p c * fn b :=
  ⟨SecOps.secAdd a (SecOps.secScale (scal p c) b), rfl⟩

theorem gs_consts {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (c : R) (r : Z ⟶ X) (z : Z)
    {j : Fin 1 → L.ι} (h : r z ∈ ch L j) : gs r z (ch L j) (consts L p c j) = cst (r ≫ p) z c :=
  (gs_res r z le_top h _).trans (ExpInt.gs_scal p r z c)

theorem sw_comb {R : Type} [CommRing R] {p : X ⟶ Spec (CommRingCat.of R)} {a b d : H0 L k} {c : R}
    (e : fn d = fn a + consts L p c * fn b) (r : Z ⟶ X) (z : Z) {j : L.ι} (h : r z ∈ L.U j) :
    sw r z d j = sw r z a j + cst (r ≫ p) z c * sw r z b j := by
  rw [sw, SecRingIso.sv, e, Pi.add_apply, Pi.mul_apply, gs_add r z _ (mem_ch h), gs_mul r z _ (mem_ch h),
    gs_consts p c r z (mem_ch h)]

theorem sw_scale {R : Type} [CommRing R] {p : X ⟶ Spec (CommRingCat.of R)} {b d : H0 L k} {c : R}
    (e : fn d = consts L p c * fn b) (r : Z ⟶ X) (z : Z) {j : L.ι} (h : r z ∈ L.U j) :
    sw r z d j = cst (r ≫ p) z c * sw r z b j := by
  rw [sw, SecRingIso.sv, e, Pi.mul_apply, gs_mul r z _ (mem_ch h), gs_consts p c r z (mem_ch h)]

theorem sw_mul {a : H0 L n} {b : H0 L m} {d : H0 L k} (e : fn d = fn a * fn b) (r : Z ⟶ X) (z : Z) {j : L.ι}
    (h : r z ∈ L.U j) : sw r z d j = sw r z a j * sw r z b j := sv_mul (congrFun e) r z (mem_ch h)

theorem sw_zero {d : H0 L k} (e : fn d = 0) (r : Z ⟶ X) (z : Z) {j : L.ι} (h : r z ∈ L.U j) : sw r z d j = 0 := by
  rw [sw, SecRingIso.sv, e]; exact LBGerm.gs_zero r z _ (mem_ch h)

theorem app_eq_zero {d : H0 L k} (φ : Z ⟶ X) (h : ∀ z j, φ z ∈ L.U j → sw φ z d j = 0) (j : Fin 1 → L.ι) :
    (φ.app (ch L j)).hom (fn d j) = 0 := fn_ext fun z hz => by
  refine (gs_pull (𝟙 Z) φ z _ hz _).trans (Eq.trans ?_ (LBGerm.gs_zero (𝟙 Z) z _ hz).symm)
  have := h z (j 0) (Set.mem_iInter.1 hz 0)
  rw [Category.id_comp, fin_one j]
  exact this

theorem fn_ext' {a : H0 L k} {v : ∀ j, Γ(X, ch L j)}
    (h : ∀ x j, x ∈ L.U j → sw (𝟙 X) x a j = gs (𝟙 X) x _ (v fun _ => j)) : fn a = v :=
  funext fun j => fn_ext fun x hx => by
    have := h x (j 0) (Set.mem_iInter.1 hx 0)
    rw [fin_one j]
    exact this

def Pulls (w : LB.Iso L' (L.pull F)) (s : H0 L k) (a : H0 L' k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (i : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U i →
    sw (r ≫ F) z s j = (Geo.Tor.gw w r z j i ^ k).val * sw r z a i

theorem pulls_of {w : LB.Iso L' (L.pull F)} {s : H0 L k} {a : H0 L' k}
    (h : FamFieldPull.IsSecPull w (fun _ : Fin 1 => 𝟙 X') (fun _ => 𝟙 X) (fun _ => (k : ℤ)) F a s) : Pulls w s a :=
  fun Z r z j i hj hi => by
    have := h Z r z (fun _ => j) (fun _ => i) (fun _ => hj) (fun _ => hi)
    rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast] at this
    exact this

theorem exists_pulls (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w) (s : H0 L k) :
    ∃ a, Pulls w s a := by
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull X X' X X' L L' F hL hL' w ((isGen_iff w).2 hw) (Fin 1)
    (fun _ => 𝟙 X') (fun _ => 𝟙 X) (fun _ => (k : ℤ)) F (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) s
  exact ⟨a, pulls_of ha⟩

theorem Pulls.comp {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    (T : Tri w w' w'') (hL' : L'.IsLB) {s : H0 L k} {a : H0 L' k} {b : H0 L'' k} (h : Pulls w s a)
    (h' : Pulls w' a b) : Pulls w'' s b := fun Z r z j i hj hi => by
  obtain ⟨l, hl⟩ := exists_chart hL' (F' (r z))
  rw [← Category.assoc, h Z (r ≫ F') z j l hj hl, h' Z r z l i hl hi, T Z r z j l i hj hl hi, mul_pow, Units.val_mul,
    _root_.mul_assoc]

theorem Pulls.mul {w : LB.Iso L' (L.pull F)} {s : H0 L n} {a : H0 L' n} {t : H0 L m} {b : H0 L' m}
    {u : H0 L (n + m)} {d : H0 L' (n + m)} (h : Pulls w s a) (h' : Pulls w t b) (e : fn u = fn s * fn t)
    (e' : fn d = fn a * fn b) : Pulls w u d := fun Z r z j i hj hi => by
  rw [sw_mul e (r ≫ F) z hj, sw_mul e' r z hi, h Z r z j i hj hi, h' Z r z j i hj hi, pow_add, Units.val_mul]
  ring

theorem Pulls.zero_iff {w : LB.Iso L' (L.pull F)} (hL : L.IsLB) (hL' : L'.IsLB) {s : H0 L k} {a : H0 L' k}
    (h : Pulls w s a) (hF : ∀ W, Function.Injective (F.app W).hom) : fn a = 0 ↔ fn s = 0 := by
  refine ⟨fun e => funext fun J => hF _ ((app_eq_zero F (fun x j hj => ?_) J).trans (map_zero _).symm),
    fun e => fn_ext' fun x i hi => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL' x
    have := h _ (𝟙 X') x j i hj hi
    rwa [Category.id_comp, sw_zero e (𝟙 X') x hi, mul_zero] at this
  · obtain ⟨j, hj⟩ := exists_chart hL (F x)
    have := h _ (𝟙 X') x j i hj hi
    rw [sw_zero e (𝟙 X' ≫ F) x hj, eq_comm, Units.mul_right_eq_zero] at this
    exact this.trans (LBGerm.gs_zero (𝟙 X') x _ (mem_ch hi)).symm

theorem exists_iso_inv (hL : L.IsLB) (hL' : L'.IsLB) {p : X'' ⟶ X} {g : X'' ⟶ X'} {g' : X' ⟶ X''} (e : g' ≫ g = 𝟙 _)
    (w : LB.Iso (L.pull p) (L'.pull g)) (hw : PGen w) : ∃ v : LB.Iso L' (L.pull (g' ≫ p)), PGen v ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (i : L'.ι), p (g' (r z)) ∈ L.U j → r z ∈ L'.U i →
        Geo.Tor.gw v r z j i = (Geo.Tor.gw w (r ≫ g') z i (fun _ => j))⁻¹ := by
  obtain ⟨v₀, h₀, e₀⟩ := RigidSections.exists_invIso w hw g' e
  let t : LB.Iso (L.pull p) (L.pull p) := ⟨fun q => (L.pull p).g q.1 q.2⟩
  have vt : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) (j : L.ι) (J : PUnit → L.ι), p (r z) ∈ L.U j →
      r z ∈ (L.pull p).U J → Geo.Tor.gw t r z j J = gm (r ≫ p) z _ (L.g j (J PUnit.unit)) := fun Z r z j J hj hJ =>
    gm_pull_g L p r z (fun _ => j) J (mem_pull.2 hj) hJ
  have ht : PGen t := fun Z r z j j' J J' hj hj' hJ hJ' => by
    rw [vt Z r z j J hj hJ, vt Z r z j' J' hj' hJ', gm_pull_g L p r z J J' hJ hJ',
      ← gm_cocycle hL (r ≫ p) z hj' ((mem_pull (F := p)).1 hJ) ((mem_pull (F := p)).1 hJ'),
      ← gm_cocycle hL (r ≫ p) z hj hj' ((mem_pull (F := p)).1 hJ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨v, T⟩ := exists_comp (pull_isLB hL p) t v₀ ht h₀ hL hL'
  refine ⟨v, T.pgen_comp (pull_isLB hL p) ht h₀, fun Z r z j i hj hi => ?_⟩
  rw [T Z r z j (fun _ => j) i hj (mem_pull.2 hj) hi, vt Z (r ≫ g') z j _ hj (mem_pull.2 hj),
    gm_self hL ((r ≫ g') ≫ p) z hj, _root_.one_mul, e₀ Z r z i (fun _ => j) (mem_pull.2 hj) hi]

theorem exists_reindex (s : H0 (L.pull F) k) :
    ∃ t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => F) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
        gs r z (LB.wchart L (fun _ : Fin 1 => F) (fun _ => j)) (t.f fun _ => j) = sw r z s (fun _ => j) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => F) j ≤ ch (L.pull F) (fun _ _ => j 0) := fun j x hx =>
    mem_ch (L := L.pull F) (mem_pull.2 (Set.mem_iInter.1 hx 0))
  refine ⟨LBGerm.secOfGerm (M := LB.LinComb L (K := Fin 1) (fun _ => F) (fun _ => (k : ℤ)))
    (fun j => (X'.presheaf.map (homOfLE (le j)).op).hom (fn s _)) fun y i j hi hj => ?_,
    fun Z r z j hj => gs_res r z (le _) (Set.mem_iInter.2 fun _ => hj) _⟩
  refine (gs_res (𝟙 X') y (le i) hi _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val
    (gm_linComb L (fun _ : Fin 1 => F) _ (𝟙 X') y i j hi hj)) (gs_res (𝟙 X') y (le j) hj _)).symm)
  refine (sec_trans s (𝟙 X') y (le i hi) (le j hj)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
  refine (Fin.prod_univ_one _).trans (Eq.trans ?_ (Fin.prod_univ_one _).symm)
  exact congrArg (· ^ (k : ℤ)) ((gm_pull_g L F (𝟙 X' ≫ 𝟙 X') y (fun _ => i 0) (fun _ => j 0)
    (mem_pull.2 (Set.mem_iInter.1 hi 0)) (mem_pull.2 (Set.mem_iInter.1 hj 0))).trans (by rw [Category.comp_id]))

end General

section Relations

variable {W X X' X'' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {k n m : ℕ}
  {R S : Type} [CommRing R] [CommRing S]

theorem Pulls.comb {w : LB.Iso L' (L.pull F)} {p : X ⟶ Sp R} {p' : X' ⟶ Sp S} {φ : R →+* S}
    (hp : F ≫ p = p' ≫ spMap φ) {s t u : H0 L k} {a b d : H0 L' k} {c : R} (h : Pulls w s a) (h' : Pulls w t b)
    (e : fn u = fn s + consts L p c * fn t) (e' : fn d = fn a + consts L' p' (φ c) * fn b) : Pulls w u d :=
  fun Z r z j i hj hi => by
    rw [sw_comb e (r ≫ F) z hj, sw_comb e' r z hi, h Z r z j i hj hi, h' Z r z j i hj hi, Category.assoc, hp,
      ← Category.assoc, cst_comp]
    ring

theorem Pulls.scale {w : LB.Iso L' (L.pull F)} {p : X ⟶ Sp R} {p' : X' ⟶ Sp S} {φ : R →+* S}
    (hp : F ≫ p = p' ≫ spMap φ) {t u : H0 L k} {b d : H0 L' k} {c : R} (h' : Pulls w t b)
    (e : fn u = consts L p c * fn t) (e' : fn d = consts L' p' (φ c) * fn b) : Pulls w u d :=
  fun Z r z j i hj hi => by
    rw [sw_scale e (r ≫ F) z hj, sw_scale e' r z hi, h' Z r z j i hj hi, Category.assoc, hp,
      ← Category.assoc, cst_comp]
    ring

theorem exists_scale (p : X ⟶ Sp R) (b : H0 L k) (c : R) : ∃ d : H0 L k, fn d = consts L p c * fn b :=
  ⟨SecOps.secScale (scal p c) b, rfl⟩

theorem pulls_of_secScal (hL : L.IsLB) {p : X'' ⟶ X} {g : X'' ⟶ X'} {g' : X' ⟶ X''} (e : g' ≫ g = 𝟙 _)
    {w : LB.Iso (L.pull p) (L'.pull g)} {v : LB.Iso L' (L.pull (g' ≫ p))}
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (i : L'.ι), p (g' (r z)) ∈ L.U j → r z ∈ L'.U i →
      Geo.Tor.gw v r z j i = (Geo.Tor.gw w (r ≫ g') z i (fun _ => j))⁻¹)
    {a b : H0 L' k} {s : H0 (L.pull p) k} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ)))}
    {σ : H0 L k} (hs : Pulls w a s)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) (j : L.ι), p (r z) ∈ L.U j →
      gs r z (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (t.f fun _ => j) = sw r z s (fun _ => j))
    {q : X'' ⟶ Sp R} {q' : X' ⟶ Sp S} {φ : R →+* S} (hq : g' ≫ q = q' ≫ spMap φ) {c : R}
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => p) (fun _ => (k : ℤ)) t (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) σ p (scal q c))
    (hb : fn b = consts L' q' (φ c) * fn a) : Pulls v σ b := fun Z r z j i hj hi => by
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : Unit => (r ≫ g') ≫ p) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have e₁ := ExpInt.secScal_sval h (r ≫ g') z hJ
  rw [sval_of σ _ z J (fun _ => j) (fun _ => by rw [Category.comp_id]; exact eJ ()),
    sval_of t _ z J (fun _ => j) (fun _ => eJ ()), ht Z (r ≫ g') z j hj, ExpInt.gs_scal, Category.assoc r g' q, hq,
    ← Category.assoc, cst_comp, Category.assoc] at e₁
  have e₂ := hs Z (r ≫ g') z i (fun _ => j)
    (by show (g' ≫ g) (r z) ∈ _; rw [e]; exact hi) (mem_pull.2 hj)
  rw [Category.assoc, e, Category.comp_id] at e₂
  rw [hv Z r z j i hj hi, sw_scale hb r z hi, e₂, inv_pow, mul_left_comm, Units.inv_mul_cancel_left]
  exact e₁

def Agr {Idx : Type} (φ : W ⟶ X) (φ' : W ⟶ X') (C : W → Idx → Prop)
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ W) (z : Z), Idx → L.ι → (Z.presheaf.stalk z)ˣ)
    (u' : ∀ (Z : Scheme.{0}) (_ : Z ⟶ W) (z : Z), Idx → L'.ι → (Z.presheaf.stalk z)ˣ) (σ : H0 L k) (σ' : H0 L' k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : Idx) (j : L.ι) (j' : L'.ι), C (r z) i → φ (r z) ∈ L.U j →
    φ' (r z) ∈ L'.U j' → (u Z r z i j ^ k).val * sw (r ≫ φ) z σ j = (u' Z r z i j' ^ k).val * sw (r ≫ φ') z σ' j'

variable {Idx : Type} {φ : W ⟶ X} {φ' : W ⟶ X'} {C : W → Idx → Prop}
  {u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ W) (z : Z), Idx → L.ι → (Z.presheaf.stalk z)ˣ}
  {u' : ∀ (Z : Scheme.{0}) (_ : Z ⟶ W) (z : Z), Idx → L'.ι → (Z.presheaf.stalk z)ˣ}

theorem Agr.symm {σ : H0 L k} {σ' : H0 L' k} (h : Agr φ φ' C u u' σ σ') : Agr φ' φ C u' u σ' σ :=
  fun Z r z i j' j hC hj' hj => (h Z r z i j j' hC hj hj').symm

theorem Agr.comb {p : X ⟶ Sp R} {p' : X' ⟶ Sp R} (hp : φ ≫ p = φ' ≫ p') {s t d : H0 L k} {s' t' d' : H0 L' k} {c : R}
    (h : Agr φ φ' C u u' s s') (h' : Agr φ φ' C u u' t t') (e : fn d = fn s + consts L p c * fn t)
    (e' : fn d' = fn s' + consts L' p' c * fn t') : Agr φ φ' C u u' d d' := fun Z r z i j j' hC hj hj' => by
  rw [sw_comb e (r ≫ φ) z hj, sw_comb e' (r ≫ φ') z hj', Category.assoc, Category.assoc, hp]
  linear_combination h Z r z i j j' hC hj hj' + cst (r ≫ φ' ≫ p') z c * h' Z r z i j j' hC hj hj'

theorem Agr.mul {s : H0 L n} {t : H0 L m} {d : H0 L (n + m)} {s' : H0 L' n} {t' : H0 L' m} {d' : H0 L' (n + m)}
    (h : Agr φ φ' C u u' s s') (h' : Agr φ φ' C u u' t t') (e : fn d = fn s * fn t)
    (e' : fn d' = fn s' * fn t') : Agr φ φ' C u u' d d' := fun Z r z i j j' hC hj hj' => by
  rw [sw_mul e (r ≫ φ) z hj, sw_mul e' (r ≫ φ') z hj', pow_add, pow_add, Units.val_mul, Units.val_mul,
    _root_.mul_mul_mul_comm, h Z r z i j j' hC hj hj', h' Z r z i j j' hC hj hj', _root_.mul_mul_mul_comm]

theorem Agr.zero (hL' : L'.IsLB) (hC : ∀ y, ∃ i, C y i) {s : H0 L k} {s' : H0 L' k} (h : Agr φ φ' C u u' s s')
    (e : fn s' = 0) (j) : (φ.app (ch L j)).hom (fn s j) = 0 := app_eq_zero φ (fun y j hj => by
  obtain ⟨i, hi⟩ := hC y
  obtain ⟨j', hj'⟩ := exists_chart hL' (φ' y)
  have := h W (𝟙 W) y i j j' hi hj hj'
  rwa [sw_zero e (𝟙 W ≫ φ') y hj', mul_zero, Units.mul_right_eq_zero, Category.id_comp] at this) j

end Relations

theorem exists_iso_of_rel (hL : Laws) {R : Type} [CommRing R] [IsDomain R] {X X' : Scheme.{0}} (p : X ⟶ Sp R)
    (p' : X' ⟶ Sp R) {L : LB X} {L' : LB X'} (l : L.IsLB) (l' : L'.IsLB) (A A' : PolAV (Sp (FractionRing R)))
    {ψ : A.A.left ⟶ X} {ψ' : A'.A.left ⟶ X'} (hψ : ψ ≫ p = A.A.hom ≫ spMap (algebraMap R _))
    (hψ' : ψ' ≫ p' = A'.A.hom ≫ spMap (algebraMap R _)) (inj : ∀ W, Function.Injective (ψ.app W).hom)
    (inj' : ∀ W, Function.Injective (ψ'.app W).hom) {v : LB.Iso A.L (L.pull ψ)} {v' : LB.Iso A'.L (L'.pull ψ')}
    (hv : PGen v) (hv' : PGen v')
    (lf : ∀ k, 1 ≤ k → ∀ a : H0 A.L k, ∃ c : R, c ≠ 0 ∧ ∃ (σ : H0 L k) (b : H0 A.L k), Pulls v σ b ∧
      fn b = consts A.L A.A.hom (algebraMap R _ c) * fn a)
    (lf' : ∀ k, 1 ≤ k → ∀ a : H0 A'.L k, ∃ c : R, c ≠ 0 ∧ ∃ (σ : H0 L' k) (b : H0 A'.L k), Pulls v' σ b ∧
      fn b = consts A'.L A'.A.hom (algebraMap R _ c) * fn a)
    (Ag : ∀ k, H0 L' k → H0 L k → Prop)
    (hc : ∀ k (c : R) s' s t' t d' d, Ag k s' s → Ag k t' t → fn d' = fn s' + consts L' p' c * fn t' →
      fn d = fn s + consts L p c * fn t → Ag k d' d)
    (hm : ∀ n m s' s t' t d' d, Ag n s' s → Ag m t' t → fn d' = fn s' * fn t' → fn d = fn s * fn t → Ag (n + m) d' d)
    (hz : ∀ k s' s, Ag k s' s → (fn s' = 0 ↔ fn s = 0))
    (he : ∀ k, 1 ≤ k → ∀ s : H0 L k, ∃ c : R, c ≠ 0 ∧ ∃ t' t, Ag k t' t ∧ fn t = consts L p c * fn s)
    (he' : ∀ k, 1 ≤ k → ∀ s' : H0 L' k, ∃ c : R, c ≠ 0 ∧ ∃ t' t, Ag k t' t ∧ fn t' = consts L' p' c * fn s') :
    ∃ (Φ : A'.A ≅ A.A) (w : LB.Iso A'.L (A.L.pull Φ.hom.left)), PGen w ∧ ∀ k, 1 ≤ k → ∀ σ' σ a' a, Ag k σ' σ →
      Pulls v' σ' a' → Pulls v σ a → Pulls w a a' := by
  let T : ∀ k : ℕ, H0 A'.L k → H0 A.L k → Prop := fun k a' a => ∃ σ' σ, Ag k σ' σ ∧ Pulls v' σ' a' ∧ Pulls v σ a
  have H := fun k (hk : 1 ≤ k) => exists_equiv (R := R) (consts A.L A.A.hom) (consts A'.L A'.A.hom)
    (fn : H0 A.L k → _) (fn : H0 A'.L k → _) fn_injective
    fn_injective (exists_comb _) (exists_comb _) (T k)
    (by
      rintro c a' a b' b ⟨s', s, h₁, h₂, h₃⟩ ⟨t', t, k₁, k₂, k₃⟩
      obtain ⟨u, e⟩ := exists_comb p s t c
      obtain ⟨u', e'⟩ := exists_comb p' s' t' c
      obtain ⟨d, f⟩ := exists_comb A.A.hom a b (algebraMap R _ c)
      obtain ⟨d', f'⟩ := exists_comb A'.A.hom a' b' (algebraMap R _ c)
      exact ⟨d', d, ⟨u', u, hc k c _ _ _ _ _ _ h₁ k₁ e' e, h₂.comb hψ' k₂ e' f', h₃.comb hψ k₃ e f⟩, f', f⟩)
    (by
      rintro a' a ⟨s', s, h₁, h₂, h₃⟩
      exact (h₂.zero_iff l' A'.isLB inj').trans ((hz k _ _ h₁).trans (h₃.zero_iff l A.isLB inj).symm))
    (fun a => by
      obtain ⟨c, hc, s, b, h₁, e₁⟩ := lf k hk a
      obtain ⟨d, hd, t', t, h₂, e₂⟩ := he k hk s
      obtain ⟨b', h₃⟩ := exists_pulls l' A'.isLB hv' t'
      obtain ⟨b₁, e₃⟩ := exists_scale A.A.hom b (algebraMap R _ d)
      exact ⟨d * c, mul_ne_zero hd hc, b', b₁, ⟨t', t, h₂, h₃, h₁.scale hψ e₂ e₃⟩, by
        rw [e₃, e₁, map_mul, map_mul, _root_.mul_assoc]⟩)
    (fun a => by
      obtain ⟨c, hc, s, b, h₁, e₁⟩ := lf' k hk a
      obtain ⟨d, hd, t', t, h₂, e₂⟩ := he' k hk s
      obtain ⟨b', h₃⟩ := exists_pulls l A.isLB hv t
      obtain ⟨b₁, e₃⟩ := exists_scale A'.A.hom b (algebraMap R _ d)
      exact ⟨d * c, mul_ne_zero hd hc, b₁, b', ⟨t', t, h₂, h₁.scale hψ' e₂ e₃, h₃⟩, by
        rw [e₃, e₁, map_mul, map_mul, _root_.mul_assoc]⟩)
  choose θ h₁ h₂ using H
  obtain ⟨Φ, w, hw, h⟩ := exists_iso_of_polAV_sectionRing hL _ A A' θ
    (fun n hn c a b d e => congrFun (h₂ n hn c a b d (funext e))) (fun n m hn hm' a' b' d' e => by
      obtain ⟨c₁, n₁, x', x, ⟨s', s, i₁, i₂, i₃⟩, e₁', e₁⟩ := (h₁ n hn a' _).1 rfl
      obtain ⟨c₂, n₂, y', y, ⟨t', t, k₁, k₂, k₃⟩, e₂', e₂⟩ := (h₁ m hm' b' _).1 rfl
      obtain ⟨u, f₁⟩ := exists_mul s t
      obtain ⟨u', f₂⟩ := exists_mul s' t'
      obtain ⟨q, f₃⟩ := exists_mul x y
      obtain ⟨q', f₄⟩ := exists_mul x' y'
      obtain ⟨d, f₅⟩ := exists_mul (θ n hn a') (θ m hm' b')
      have e' : fn d' = fn a' * fn b' := funext e
      have g₃ : fn q = fn x * fn y := funext f₃
      have g₄ : fn q' = fn x' * fn y' := funext f₄
      have g₅ : fn d = fn (θ n hn a') * fn (θ m hm' b') := funext f₅
      rw [(h₁ (n + m) _ d' d).2 ⟨c₁ * c₂, mul_ne_zero n₁ n₂, q', q, ⟨u', u,
        hm _ _ _ _ _ _ _ _ i₁ k₁ (funext f₂) (funext f₁), i₂.mul k₂ (funext f₂) g₄, i₃.mul k₃ (funext f₁) g₃⟩,
        by rw [g₄, e', e₁', e₂', map_mul, map_mul, _root_.mul_mul_mul_comm],
        by rw [g₃, g₅, e₁, e₂, map_mul, map_mul, _root_.mul_mul_mul_comm]⟩]
      exact f₅)
  refine ⟨Φ, w, (isGen_iff w).1 hw, fun k hk σ' σ a' a i₁ i₂ i₃ => ?_⟩
  obtain rfl := (h₁ k hk a' a).2 ⟨1, one_ne_zero, a', a, ⟨σ', σ, i₁, i₂, i₃⟩, by
    rw [map_one, map_one, _root_.one_mul], by rw [map_one, map_one, _root_.one_mul]⟩
  exact pulls_of (h k hk a')

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I D A G)

theorem inv_gen : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id

theorem gen_inv : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.hom_inv_id

theorem gen_over : U.gen.inv.left ≫ pullback.snd G.hom (jK R) ≫ jK R = A.A.hom ≫ spMap (algebraMap R _) :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w U.gen.inv))

theorem gen_over' : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ spMap (algebraMap R _) :=
  (Category.assoc _ _ _).trans ((congrArg (U.gen.inv.left ≫ ·) pullback.condition).trans (gen_over U))

theorem gen_injective (W : G.left.Opens) :
    Function.Injective ((U.gen.inv.left ≫ pullback.fst G.hom (jK R)).app W).hom := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  exact (ConcreteCategory.bijective_of_isIso (U.gen.inv.left.app _)).1.comp (ExpInt.generic_app_injective G W)

theorem exists_compare : ∃ (w : LB.Iso (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left))
    (v : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), PGen w ∧ PGen v ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      pullback.fst G.hom (jK R) (U.gen.inv.left (r z)) ∈ U.LG.L.U j → r z ∈ A.L.U i →
      Geo.Tor.gw v r z j i = (Geo.Tor.gw w (r ≫ U.gen.inv.left) z i (fun _ => j))⁻¹) ∧
    ∀ k, 1 ≤ k → ∀ a : H0 A.L k, ∃ c : R, c ≠ 0 ∧ ∃ (σ : H0 U.LG.L k) (b : H0 A.L k), Pulls v σ b ∧
      fn b = consts A.L A.A.hom (algebraMap R _ c) * fn a := by
  obtain ⟨w, hw⟩ := LBIso.symm U.ext
  have hw := (isGen_iff w).1 hw
  obtain ⟨v, hv, e⟩ := exists_iso_inv U.LG.isLB A.isLB (inv_gen U) w hw
  refine ⟨w, v, hw, hv, e, fun k hk a => ?_⟩
  obtain ⟨s, hs⟩ := exists_pulls A.isLB (pull_isLB U.LG.isLB _) hw a
  obtain ⟨t, ht⟩ := exists_reindex s
  obtain ⟨E, ⟨c, hc, σ, -, h, -⟩, -⟩ := (U.expand k hk).1 t
  obtain ⟨b, hb⟩ := exists_scale A.A.hom a (algebraMap R _ c)
  exact ⟨c, hc, σ, b, pulls_of_secScal U.LG.isLB (inv_gen U) e hs ht (gen_over U) h hb, hb⟩

end Unif

theorem exists_move {X X' Y Y' W' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB Y} {M' : LB Y'} (l : L.IsLB)
    (l' : L'.IsLB) (m : M.IsLB) (m' : M'.IsLB) {ψ : Y ⟶ X} {p : W' ⟶ X'} {g : W' ⟶ Y'} {g' : Y' ⟶ W'}
    (e : g ≫ g' = 𝟙 _) {Φ : Y' ⟶ Y} {v : LB.Iso M (L.pull ψ)} (hv : PGen v) {w₀ : LB.Iso M' (M.pull Φ)} (h₀ : PGen w₀)
    {w : LB.Iso (L'.pull p) (M'.pull g)} (hw : PGen w) {v' : LB.Iso M' (L'.pull (g' ≫ p))}
    (hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : L'.ι) (i : M'.ι), p (g' (r z)) ∈ L'.U j → r z ∈ M'.U i →
      Geo.Tor.gw v' r z j i = (Geo.Tor.gw w (r ≫ g') z i (fun _ => j))⁻¹) (F : W' ⟶ X) (hF : F = g ≫ Φ ≫ ψ) :
    ∃ u : LB.Iso (L'.pull p) (L.pull F), u.IsGen ∧ ∀ (k : ℕ) (σ : H0 L k) (σ' : H0 L' k) (a : H0 M k) (a' : H0 M' k),
      Pulls v σ a → Pulls w₀ a a' → Pulls v' σ' a' → ∀ (Z : Scheme.{0}) (r : Z ⟶ W') (z : Z) (j : L.ι) (j' : L'.ι),
        F (r z) ∈ L.U j → p (r z) ∈ L'.U j' →
        sw (r ≫ F) z σ j = (Geo.Tor.gw u r z j (fun _ => j') ^ k).val * sw (r ≫ p) z σ' j' := by
  subst hF
  obtain ⟨w₁, T₁⟩ := exists_comp m v w₀ hv h₀ l m'
  have h₁ := T₁.pgen_comp m hv h₀
  obtain ⟨u, T⟩ := exists_comp m' w₁ w h₁ hw l (pull_isLB l' p)
  refine ⟨u, (isGen_iff u).2 (T.pgen_comp m' h₁ hw), fun k σ σ' a a' i₁ i₂ i₃ Z r z j j' hj hj' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart m' (g (r z))
  have hp : p (g' (g (r z))) ∈ L'.U j' := by
    show (g ≫ g' ≫ p) (r z) ∈ _
    rw [← Category.assoc, e, Category.id_comp]; exact hj'
  have e₁ := (i₁.comp T₁ m i₂) Z (r ≫ g) z j i hj hi
  have e₂ := i₃ Z (r ≫ g) z j' i hp hi
  rw [hv' Z (r ≫ g) z j' i hp hi, Category.assoc, Category.assoc, ← Category.assoc g, e, Category.id_comp,
    Category.comp_id] at e₂
  rw [Category.assoc] at e₁
  rw [e₁, e₂, T Z r z j i (fun _ => j') hj hi (mem_pull.2 hj'), mul_pow, Units.val_mul, inv_pow, _root_.mul_assoc,
    Units.mul_inv_cancel_left]

end GlobalTheory.RigidGeneric

namespace GlobalTheory

open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_genericFibre_iso_of_thickenings : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∃ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) := by
  intro hL hL₂ R _ _ _ I hI hm D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj
  have en := integral_sections_correspond hL hL₂ R I hI hm D D' A A' G G' hG hG' U U' hD j hj
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := hm.le.trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory
