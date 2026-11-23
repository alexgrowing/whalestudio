import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Algebra

theorem level_split (l : Level H) :
    ∃ u ∈ l.Mb, ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), u + v = 1 := by
  have h : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  exact Submodule.mem_sup.1 h

theorem mem_of_modN (l : Level H) {x : D.La} (h : D.ModN l.M x) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := h
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_inf.trans inf_le_left
    rw [l.prod] at h
    exact h (Ideal.subset_span rfl)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM trivial

theorem level_pos (l : Level H) : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

theorem sub_eq_one {Q : Type} [Group Q] (P : D.La → Q) (hP : ∀ a b, P (a + b) = P a * P b) {a b : D.La}
    (h : P a = P b) : P (a - b) = 1 := by
  have := hP (a - b) b
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem modN_of_ev_eq (J : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {a b : D.La} (h : J.ev n a = J.ev n b) :
    D.ModN n (a - b) :=
  (J.ker n hn _).1 (sub_eq_one _ (J.add n) h)

theorem ev_pow_div (J : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    J.ev N a ^ (N / n) = J.ev n a := by
  obtain ⟨d, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hN
  have hd : 0 < d := Nat.pos_of_mul_pos_left hN
  rw [Nat.mul_div_cancel_left _ hn]
  exact J.tower n d hn hd a

theorem mem_of_eq_one (l : Level H) (J : TateIso D k Q act e) (P : D.La → Q) (hP : ∀ a b, P (a + b) = P a * P b)
    (hk : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), P a = 1)
    (hJ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P a = J.ev l.M a)
    {c : D.La} (hc : P c = 1) : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨u, hu, v, hv, huv⟩ := level_split l
  have hcs : c = u • c + v • c := by rw [← add_smul, huv, one_smul]
  have h1 : u • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hu trivial
  have h2 : J.ev l.M (v • c) = 1 := by
    rw [← hJ _ (Submodule.smul_mem_smul hv trivial)]
    rw [hcs, hP, hk _ h1, _root_.one_mul] at hc
    exact hc
  rw [hcs]
  exact Submodule.add_mem _ h1 (mem_of_modN l ((J.ker _ (level_pos l) _).1 h2))

theorem inGam_of_diff (l l₂ : Level H) (hd : l.Dvd l₂) (J J' : TateIso D k Q act e) (g : Sim D)
    (hg : ∀ n, 0 < n → (∀ a, J'.ev n a = J.ev n (g.f n a)) ∧ J'.ζ n = J.ζ n ^ g.ν n)
    (hζ : J'.ζ l₂.A = J.ζ l₂.A) (P P' : D.La → Q)
    (hP : ∀ a b, P (a + b) = P a * P b) (hP' : ∀ a b, P' (a + b) = P' a * P' b)
    (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P a = 1)
    (hk' : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P' a = 1)
    (hJ : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P a = J.ev l₂.M a)
    (hJ' : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P' a = J'.ev l₂.M a)
    (hM : ∀ a, P a ^ (l₂.M / l.M) = P' a ^ (l₂.M / l.M))
    (hA : ∀ a, J.ev l₂.A a ^ (l₂.A / l.A) = J'.ev l₂.A a ^ (l₂.A / l.A)) :
    g.InGam l l₂ ∧ ∀ a, P' a = P (g.f l₂.M a) := by
  obtain ⟨u, hu, v, hv, huv⟩ := level_split l₂
  have hcs : ∀ c : D.La, c = u • c + v • c := fun c => by rw [← add_smul, huv, one_smul]
  refine ⟨⟨?_, fun a => ?_, fun a => ?_⟩, fun a => ?_⟩
  · rw [← (J.ζ_prim _ l₂.A_pos).zpow_eq_one_iff_dvd, zpow_sub_one, ← (hg _ l₂.A_pos).2, hζ, mul_inv_cancel]
  · have h := hM (v • a)
    rw [hJ _ (Submodule.smul_mem_smul hv trivial), hJ' _ (Submodule.smul_mem_smul hv trivial),
      ev_pow_div J (level_pos l₂) hd.1, ev_pow_div J' (level_pos l₂) hd.1, (hg _ (level_pos l)).1] at h
    have h2 := mem_of_modN l (modN_of_ev_eq J (level_pos l) h.symm)
    rw [map_smul, ← smul_sub] at h2
    rw [hcs (g.f l.M a - a)]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul (hd.2.1 hu) trivial) h2
  · have h := hA a
    rw [ev_pow_div J l₂.A_pos hd.2.2, ev_pow_div J' l₂.A_pos hd.2.2, (hg _ l.A_pos).1] at h
    exact modN_of_ev_eq J l.A_pos h.symm
  · rw [hcs a, hP', hk' _ (Submodule.smul_mem_smul hu trivial), map_add, hP, map_smul, map_smul,
      hk _ (Submodule.smul_mem_smul hu trivial), hJ _ (Submodule.smul_mem_smul hv trivial),
      hJ' _ (Submodule.smul_mem_smul hv trivial), (hg _ (level_pos l₂)).1, map_smul]

theorem sub_mem_of_inGam {l l₂ : Level H} (hd : l.Dvd l₂) {g : Sim D} (hg : g.InGam l l₂) (a : D.La) :
    g.f l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨d, hdd⟩ := hd.1
  have hd0 : 0 < d := Nat.pos_of_mul_pos_left (hdd ▸ level_pos l₂)
  have h := mem_of_modN l (g.tower l.M d (level_pos l) hd0 a)
  rw [← hdd] at h
  have := Submodule.add_mem _ h (hg.2.1 a)
  rwa [sub_add_sub_cancel] at this

def tateTransport {Q' : Type} [Group Q'] {act' : 𝓞 E → Q' → Q'} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIso D k Q act e) (φ : Q ≃* Q') (hact : ∀ c x, φ (act c x) = act' c (φ x))
    (he : ∀ n x y c, e n x y c → e' n (φ x) (φ y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := φ (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, hact]
  ker n hn a := by rw [map_eq_one_iff φ φ.injective, I.ker n hn]
  onto n hn x := by
    obtain ⟨x, rfl⟩ := φ.surjective x
    rw [← map_pow, map_eq_one_iff φ φ.injective, I.onto n hn]
    exact exists_congr fun a => φ.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he _ _ _ _ (I.isom n hn a b)

end Algebra

section Points

variable {S S' T : Scheme.{0}}

theorem unit_left {G : Over S} (x : T ⟶ S) (σ : 𝟙_ (Over S) ⟶ G) :
    (toUnit (Over.mk x) ≫ σ).left = x ≫ σ.left := by
  have h : (toUnit (Over.mk x)).left = x := by
    have := Over.w (toUnit (Over.mk x))
    simpa using this
  rw [Over.comp_left, h]

theorem sec_w {G : Over S} (σ : 𝟙_ (Over S) ⟶ G) : σ.left ≫ G.hom = 𝟙 S := Over.w σ

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (x : T ⟶ S') (z : T ⟶ S) (hz : x ≫ f = z) :
    ∃ e : (Over.mk x ⟶ G') ≃* (Over.mk z ⟶ G), ∀ p, (e p).left = p.left ≫ φ := by
  subst hz
  let F : (Over.mk x ⟶ G') →* (Over.mk (x ≫ f) ⟶ G) := MonoidHom.mk' (fun p => pushPt h.1.w p) fun p q =>
    Over.OverMorphism.ext (h.2 _ p q (pushPt h.1.w p) (pushPt h.1.w q) rfl rfl).symm
  refine ⟨MulEquiv.ofBijective F ⟨fun p q hpq => ?_, fun q => ?_⟩, fun p => rfl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun w => w.left) hpq
    · rw [Over.w, Over.w]
  · refine ⟨Over.homMk (h.1.lift q.left x (Over.w q)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    exact h.1.lift_fst _ _ _

theorem sab_cast {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (h : f = f') (m : SABMap t' t f) :
    ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

end Points

section Main

theorem exists_tate_push
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S') (z : Sp k ⟶ S) (hz : x ≫ f = z) (e : (Over.mk x ⟶ t'.G) ≃* (Over.mk z ⟶ t.G))
    (he : ∀ p, (e p).left = p.left ≫ m.φ)
    (I : TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), J.ζ = I.ζ ∧ ∀ n a, J.ev n a = e (I.ev n a) := by
  subst hz
  refine ⟨tateTransport I e (fun c p => Over.OverMorphism.ext ?_) (fun n p q c h => ?_), rfl, fun _ _ => rfl⟩
  · rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]
    exact congrArg _ (m.act c)
  · obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ t.PP.isLB t'.PP.isLB m.cart ⟨w, (isGen_iff w).2 hw⟩ (Over.mk x) n p q (e p) (e q) _
      (he p) (he q)).1 h

theorem unitOn_injective {k : Type} [Field k] : Function.Injective (unitOn (R := k)) := by
  intro a b h
  apply Units.ext
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h)

variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem trivAt_of_fixed
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X), ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z))
    (hRig : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X) (o' : Obj D l (baseKA l) (z ≫ Xo.s)) (m m' : SABMap o'.t Xo.univ.t z),
      (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.X) (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X) (hg : g.InGam l l₂)
    (hρ : Xo₂.LevAut g ρ) (hx : x ≫ ρ.hom = x) : g.TrivAt l₂ := by
  obtain ⟨-, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k (x ≫ r)
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  obtain ⟨n₃, hn₃⟩ := sab_cast hx n₂
  obtain ⟨n₄, hn₄⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₃
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨eν, heν⟩ := exists_ptEquiv ν.cart x x hx
  let P : D.La → (Over.mk x ⟶ Xo₂.univ.t.G) := fun a => toUnit _ ≫ Xo₂.univ.eta a
  let PA : D.La → (Over.mk x ⟶ Xo₂.univ.t.G) := fun a => toUnit _ ≫ Xo₂.univ.etaA a
  have hP : ∀ a b, P (a + b) = P a * P b := fun a b => by
    simp only [P]; rw [Xo₂.univ.eta_add, MonObj.comp_mul]
  have hPpow : ∀ a, (P a ^ (l₂.M / l.M)).left = x ≫ (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    simp only [P]; rw [← MonObj.comp_pow, unit_left]
  have hPe : ∀ a, e (P a ^ (l₂.M / l.M)) = toUnit _ ≫ Xo.univ.eta a := fun a => by
    apply Over.OverMorphism.ext
    rw [he, hPpow, unit_left, Category.assoc, Category.assoc]
    exact congrArg _ (hm a)
  have hPν : ∀ a, eν (P (g.f l₂.M a)) = P a := fun a => by
    apply Over.OverMorphism.ext
    simp only [P]
    rw [heν, unit_left, unit_left, Category.assoc]
    exact (congrArg _ (hν a)).trans (by rw [← Category.assoc, hx])
  have hPAν : ∀ a, eν (PA (g.f l₂.A a)) = PA a := fun a => by
    apply Over.OverMorphism.ext
    simp only [PA]
    rw [heν, unit_left, unit_left, Category.assoc]
    exact (congrArg _ (hνA a)).trans (by rw [← Category.assoc, hx])
  have hfix : ∀ a, eν (P a ^ (l₂.M / l.M)) = P a ^ (l₂.M / l.M) := fun a => by
    have h : P (g.f l₂.M a) ^ (l₂.M / l.M) = P a ^ (l₂.M / l.M) := by
      apply e.injective
      rw [hPe, hPe, ← sub_add_cancel (g.f l₂.M a) a, Xo.univ.eta_add, Xo.univ.eta_ker _ (sub_mem_of_inGam hd hg a),
        _root_.one_mul]
    rw [← h, map_pow, hPν, h]
  have hon : ∀ a, (o.eta a).left ≫ n.φ = (P a ^ (l₂.M / l.M)).left := fun a => by
    apply m.cart.1.hom_ext
    · rw [← he, hPe, unit_left, Category.assoc]
      exact (congrArg _ hn.symm).trans (p.eta a)
    · rw [Over.w, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w]; exact (Category.id_comp x).symm
  have hrig : p.toSABMap.φ = n₄.φ := hRig k _ o p.toSABMap n₄ fun a => ⟨_, rfl, by
    rw [hn₄, hn₃, hn₂, hn, ← Category.assoc, ← Category.assoc, ← Category.assoc, hon, ← heν, hfix]⟩
  have hnν : n.φ ≫ ν.φ = n.φ := by
    rw [← hn₂, ← hn₃]
    apply m.cart.1.hom_ext
    · exact hn₄.symm.trans (hrig.symm.trans hn)
    · exact n₃.cart.1.w.trans n.cart.1.w.symm
  have hid : ∀ q, eν q = q := fun q => by
    apply Over.OverMorphism.ext
    have hq : n.cart.1.lift q.left (𝟙 _) ((Over.w q).trans (Category.id_comp x).symm) ≫ n.φ = q.left :=
      n.cart.1.lift_fst _ _ _
    rw [heν, ← hq, Category.assoc]
    exact congrArg _ hnν
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, -, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  refine ⟨fun a => mem_of_eq_one l₂ I P hP (fun b hb => ?_) hI (sub_eq_one P hP ?_), fun a => ?_⟩
  · simp only [P]; rw [Xo₂.univ.eta_ker b hb, MonObj.comp_one]
  · rw [← hPν a, hid]
  · apply modN_of_ev_eq I l₂.A_pos
    rw [← hIA, ← hIA]
    exact (hid _).symm.trans (hPAν a)

end Main

end GlobalTheory.LevelFibre
