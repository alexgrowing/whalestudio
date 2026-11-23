import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.GamDat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FKstep

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

def torsRLe {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] (K : Cx.{w} R) (s : R) (n : ℕ)
    (ε : M →ₗ[R] K.X 0) : Prop :=
  (∀ x, K.d 0 (ε x) = 0) ∧ InjUpTo s ε ∧ ExactUpTo s ε (K.d 0) ∧ ∀ i ≤ n, ExactUpTo s (K.d i) (K.d (i + 1))

theorem torsRLe.mul {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] {K : Cx.{w} R} {s : R} {n : ℕ}
    {ε : M →ₗ[R] K.X 0} (h : torsRLe K s n ε) (t : R) : torsRLe K (s * t) n ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => ?_, fun y hy => ?_, fun i hi y hy => ?_⟩
  · rw [mul_comm, mul_smul, h1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩
  · obtain ⟨x, hx⟩ := h3 i hi y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩

theorem tors_resUpTo_mul {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] {K : Cx.{w} R} {s : R}
    {ε : M →ₗ[R] K.X 0} (h : K.ResUpTo s ε) (t : R) : K.ResUpTo (s * t) ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => ?_, fun y hy => ?_, fun i y hy => ?_⟩
  · rw [mul_comm, mul_smul, h1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩
  · obtain ⟨x, hx⟩ := h3 i y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩

theorem torsRLe.transfer {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type v''} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} {s s' : R} {n : ℕ}
    (h0 : InjUpTo s' (φ.mapH 0)) (hS : ∀ k ≤ n + 1, SurjUpTo s' (φ.mapH k)) (h : torsRLe K s n ε) :
    torsRLe L (s * s') n (φ.f 0 ∘ₗ ε) := by
  obtain ⟨c0, c1, c2, c3⟩ := h
  have cz : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, c0, map_zero]
  refine ⟨cz, fun x hx => ?_, fun y hy => ?_, fun i hi y hy => ?_⟩
  · have hx' : φ.f 0 (ε x) = 0 := hx
    have e1 : φ.mapH 0 (K.cls (ε x) (c0 x)) = 0 := by
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 (ε x) (c0 x) (cz x), (CrystallineSemistableComparison.P.cls_surj L 0).2.1, hx']
      exact Submodule.zero_mem _
    have e2 := h0 _ e1
    have hs : K.d 0 (s' • ε x) = 0 := by rw [map_smul, c0, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj K 0).2.2.2.2 s' (ε x) (c0 x) hs, (CrystallineSemistableComparison.P.cls_surj K 0).2.1] at e2
    have e3 : s' • ε x = 0 := (Submodule.mem_bot R).1 e2
    rw [← map_smul] at e3
    rw [mul_smul, c1 _ e3]
  · obtain ⟨z, hz⟩ := hS 0 (Nat.zero_le _) (L.cls y hy)
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 z
    have hb : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
    have hsy : L.d 0 (s' • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hb, ← (CrystallineSemistableComparison.P.cls_surj L 0).2.2.2.2 s' y hy hsy,
      (CrystallineSemistableComparison.P.cls_surj L 0).2.2.1] at hz
    have e3 : φ.f 0 a = s' • y := sub_eq_zero.1 ((Submodule.mem_bot R).1 hz)
    obtain ⟨x, hx⟩ := c2 a ha
    refine ⟨x, ?_⟩
    change φ.f 0 (ε x) = _
    rw [hx, map_smul, e3, smul_smul]
  · obtain ⟨z, hz⟩ := hS (i + 1) (by omega) (L.cls y hy)
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (i + 1)).1 z
    have hb : L.d (i + 1) (φ.f (i + 1) a) = 0 := by rw [φ.comm, ha, map_zero]
    have hsy : L.d (i + 1) (s' • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ (i + 1) a ha hb, ← (CrystallineSemistableComparison.P.cls_surj L (i + 1)).2.2.2.2 s' y hy hsy,
      (CrystallineSemistableComparison.P.cls_surj L (i + 1)).2.2.1] at hz
    obtain ⟨b, hb'⟩ := hz
    obtain ⟨c, hc⟩ := c3 i hi a ha
    refine ⟨φ.f i c - s • b, ?_⟩
    rw [map_sub, map_smul, φ.comm, hc, map_smul, hb', smul_sub, sub_sub_cancel, smul_smul]

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

def torsPi (e : ℕ) : Gam (e + 1) →* Gam e where
  toFun a := Multiplicative.ofAdd fun k => Multiplicative.toAdd a k.castSucc
  map_one' := rfl
  map_mul' _ _ := rfl

def torsLast (e : ℕ) : Gam (e + 1) →* Multiplicative ℕ where
  toFun a := Multiplicative.ofAdd (Multiplicative.toAdd a (Fin.last e))
  map_one' := rfl
  map_mul' _ _ := rfl

section Tower

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {j : C' ⥤ C} {U : UF C}

abbrev torsGp (L : Line j U) (S : C) (m : ℕ) : End (L.Ξ.obj S) := End.of (L.γ.app S) ^ m

def torsStep (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) : Gam (e + 1) →* End (L.Ξ.obj S) :=
  (MonoidHom.noncommCoprod ((L.Ξ.mapEnd S).comp (g.comp (torsPi e))) ((powersHom (End (L.Ξ.obj S)) (End.of (L.γ.app S))).comp (torsLast e))
    (fun a b => by
      refine Commute.pow_right ?_ _
      show L.γ.app S ≫ L.Ξ.map (g (torsPi e a)) = L.Ξ.map (g (torsPi e a)) ≫ L.γ.app S
      exact (L.γ.naturality _).symm)).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem torsStep_apply (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) (a : Gam (e + 1)) :
    (torsStep L g a : L.Ξ.obj S ⟶ L.Ξ.obj S) =
      (torsGp L S (Multiplicative.toAdd a (Fin.last e)) : L.Ξ.obj S ⟶ L.Ξ.obj S) ≫ L.Ξ.map (g (torsPi e a)) :=
  rfl

theorem tors_i_pow (L : Line j U) (S : C) (m : ℕ) :
    L.i.app S ≫ (torsGp L S m : L.Ξ.obj S ⟶ L.Ξ.obj S) = L.i.app S := by
  have h1 : L.i.app S ≫ L.γ.app S = L.i.app S := by
    have := congrArg (fun t => NatTrans.app t S) L.iγ
    simpa using this
  induction m with
  | zero => exact Category.comp_id _
  | succ m ih =>
    rw [torsGp, pow_succ, End.mul_def, ← Category.assoc, h1, ← torsGp, ih]

theorem tors_pow_η (L : Line j U) (S : C) (m : ℕ) :
    U.map (torsGp L S m : L.Ξ.obj S ⟶ L.Ξ.obj S) (L.η S) = U.q _ ^ m * L.η S := by
  induction m with
  | zero => rw [pow_zero, one_mul]; exact U.map_id _ _
  | succ m ih =>
    rw [torsGp, pow_succ, End.mul_def, U.map_comp, L.γη, map_mul, ← torsGp, ih, U.map_q, pow_succ', mul_assoc]

theorem tors_istep (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) (a : Gam (e + 1)) :
    L.i.app S ≫ (torsStep L g a : L.Ξ.obj S ⟶ L.Ξ.obj S) = (g (torsPi e a) : S ⟶ S) ≫ L.i.app S := by
  rw [torsStep_apply, ← Category.assoc, tors_i_pow]
  exact (L.i.naturality _).symm

theorem torsStep_gen (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) :
    (torsStep L g (gen (Fin.last e)) : L.Ξ.obj S ⟶ L.Ξ.obj S) = L.γ.app S := by
  have hp : torsPi e (gen (Fin.last e)) = 1 := by
    funext k
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last k) _
  rw [torsStep_apply, hp, map_one]
  show _ ≫ L.Ξ.map (𝟙 S) = _
  rw [L.Ξ.map_id, Category.comp_id]
  rw [show Multiplicative.toAdd (gen (Fin.last e)) (Fin.last e) = 1 from Pi.single_eq_same _ _, torsGp, pow_one]

end Tower

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

theorem tors_tower {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (U : UF C) (L : Line j U) (s : R) (n : ℕ)
    (hA : ∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) (T : C) :
    ∀ e : ℕ, ∃ (S : C) (ir : T ⟶ S) (η : Fin e → U.U S) (g : Gam e →* End S),
      (∀ a, ir ≫ (g a : S ⟶ S) = ir) ∧
      (∀ a k, U.map (g a : S ⟶ S) (η k) = U.q S ^ (Multiplicative.toAdd a k) * η k) ∧
      (∀ (t' : C') (φ : T ⟶ j.obj t') (b : Fin e → U.U (j.obj t')),
        ∃! ψ : S ⟶ j.obj t', ir ≫ ψ = φ ∧ ∀ k, U.map ψ (η k) = b k) ∧
      torsRLe (cx (SingleObj.functor g ⋙ F)) (s ^ (e * (2 * n + 5))) n
        (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) := by
  intro e
  induction e with
  | zero =>
    have : ∀ Y : SingleObj (Gam 0), Unique (SingleObj.star (Gam 0) ⟶ Y) := fun Y =>
      ⟨⟨(1 : Gam 0)⟩, fun a => show (a : Fin 0 → ℕ) = (1 : Gam 0) from funext fun k => k.elim0⟩
    have hI : Limits.IsInitial (SingleObj.star (Gam 0)) := Limits.IsInitial.ofUnique _
    refine ⟨T, 𝟙 T, fun k => k.elim0, 1, fun a => Category.comp_id _, fun a k => k.elim0,
      fun t' φ b => ⟨φ, ⟨Category.id_comp _, fun k => k.elim0⟩, fun ψ h => by rw [← h.1, Category.id_comp]⟩, ?_⟩
    have h := CrystallineSemistableComparison.P.initial (SingleObj.functor (1 : Gam 0 →* End T) ⋙ F) _ hI
    rw [zero_mul, pow_zero]
    exact ⟨h.1, h.2.1, h.2.2.1, fun i _ => h.2.2.2 i⟩
  | succ e ih =>
    obtain ⟨S, ir, η, g, h1, h2, h3, h4⟩ := ih
    refine ⟨L.Ξ.obj S, ir ≫ L.i.app S, Fin.lastCases (L.η S) (fun k => U.map (L.i.app S) (η k)), torsStep L g,
      fun a => ?_, fun a k => ?_, fun t' φ b => ?_, ?_⟩
    · rw [Category.assoc, tors_istep, ← Category.assoc, h1]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [Fin.lastCases_last]
        rw [torsStep_apply, U.map_comp, tors_pow_η, map_mul, map_pow, U.map_q, L.map_η]
      · simp only [Fin.lastCases_castSucc]
        rw [← U.map_comp, tors_istep, U.map_comp]
        erw [h2 (torsPi e a) k]
        rw [map_mul, map_pow, U.map_q]
        rfl
    · obtain ⟨χ, ⟨hχ1, hχ2⟩, hχu⟩ := h3 t' φ (fun k => b k.castSucc)
      obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := L.univ S t' χ (b (Fin.last e))
      refine ⟨ψ, ⟨by rw [Category.assoc, hψ1, hχ1], fun k => ?_⟩, fun ψ' h' => ?_⟩
      · refine Fin.lastCases ?_ (fun k => ?_) k
        · simp only [Fin.lastCases_last]; exact hψ2
        · simp only [Fin.lastCases_castSucc]; rw [← U.map_comp, hψ1]; exact hχ2 k
      · refine hψu ψ' ⟨hχu _ ⟨by rw [← Category.assoc]; exact h'.1, fun k => ?_⟩, ?_⟩
        · have := h'.2 k.castSucc
          simp only [Fin.lastCases_castSucc] at this
          rw [← U.map_comp] at this
          exact this
        · have := h'.2 (Fin.last e)
          simp only [Fin.lastCases_last] at this
          exact this
    · have hk := CrystallineSemistableComparison.B.P.kstep (SingleObj.functor g ⋙ F) (SingleObj.functor (torsStep L g) ⋙ F) (torsPi e)
        (fun a k => rfl) (F.map (L.i.app S)).hom (fun a x => by
          have h := congrArg (fun f => (F.map f).hom x) (tors_istep L g a)
          simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
          exact h.symm) s
        (by
          change Acyc1 s (F.map (L.i.app S)).hom (F.map (torsStep L g (gen (Fin.last e)))).hom
          rw [torsStep_gen]
          exact hA S) (n + 1)
      have ht := torsRLe.transfer _ (hk 0 (Nat.zero_le _)).1 (fun k hk' => (hk k hk').2) h4
      rw [← pow_add] at ht
      rw [show (e + 1) * (2 * n + 5) = e * (2 * n + 5) + (2 * (n + 1) + 3) by ring]
      convert ht using 1
      refine LinearMap.ext fun x => funext fun c => ?_
      change (F.map (ir ≫ L.i.app S)).hom x = (F.map (L.i.app S)).hom ((F.map ir).hom x)
      rw [F.map_comp]
      rfl

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.tors : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act j U d D) (L : Line j U) (s : R), Desc s F j → (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → RI (s ^ N) n F A.ι := by
  intro d n
  obtain ⟨N₀, hN₀⟩ := CrystallineSemistableComparison.B.P.gam.{w, v, u, v', u'} n
  refine ⟨(d * (2 * n + 5) + 1) * N₀, ?_⟩
  intro R _ C _ C' _ F j _ _ U D A L s hD hA
  rw [pow_mul]
  unfold Act.ι
  refine hN₀ F j (Gam d) D A.γ (s ^ (d * (2 * n + 5) + 1)) (fun T => ?_) (fun t => ?_)
  · rw [pow_succ']
    exact tors_resUpTo_mul (hD T) _
  · obtain ⟨S, ir, η, g, h1, h2, h3, h4⟩ := tors_tower F j U L s n hA (j.obj t) d
    obtain ⟨c₀⟩ := A.ne t
    have h4' := h4.mul s
    rw [← pow_succ] at h4'
    refine ⟨S, A.act η (c₀ ≫ ir), ir, g, fun a => ?_, h1, fun t' c φ => ?_, h4'.2.1, h4'.2.2.1, h4'.2.2.2⟩
    · have e1 : A.act η (c₀ ≫ ir) ≫ (g a : S ⟶ S) =
          A.act (fun k => U.q S ^ (Multiplicative.toAdd a k)) (A.act η (c₀ ≫ ir)) := by
        rw [A.act_comp, Category.assoc, h1, ← A.act_mul]
        congr 1
        funext k
        exact h2 a k
      have e2 : (A.γ a : D ⟶ D) ≫ A.act η (c₀ ≫ ir) =
          A.act (fun k => U.q S ^ (Multiplicative.toAdd a k)) (A.act η (c₀ ≫ ir)) := by
        show A.act (fun k => U.q D ^ (Multiplicative.toAdd a k)) (𝟙 D) ≫ _ = _
        rw [A.act_comp, Category.id_comp]
        congr 1
        funext k
        rw [map_pow, U.map_q]
      rw [e1, e2]
    · obtain ⟨a, ha, hau⟩ := A.trans t' (c₀ ≫ φ) c
      obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := h3 t' φ a
      refine ⟨ψ, ⟨?_, hψ1⟩, fun ψ' h' => ?_⟩
      · rw [A.act_comp, Category.assoc, hψ1, show (fun k => U.map ψ (η k)) = a from funext hψ2]
        exact ha
      · refine hψu ψ' ⟨h'.2, fun k => ?_⟩
        have hh := h'.1
        rw [A.act_comp, Category.assoc, h'.2] at hh
        exact congrFun (hau _ hh) k
