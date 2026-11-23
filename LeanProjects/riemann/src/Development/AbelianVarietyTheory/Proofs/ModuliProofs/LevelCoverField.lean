import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInducedLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

section

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {G' : Over T.left} [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem exists_secEquiv (h : IsGrpPullback G' G T.hom φ) :
    ∃ Φ : (𝟙_ (Over T.left) ⟶ G') ≃* (T ⟶ G), ∀ σ, (Φ σ).left = σ.left ≫ φ := by
  let j : T ≅ Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) := Over.isoMk (Iso.refl _) (by simp)
  let Ψ : (Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ G) ≃* (T ⟶ G) :=
    MulEquiv.ofBijective (preHom j.hom) ⟨fun x y e => (cancel_epi j.hom).1 e,
      fun y => ⟨j.inv ≫ y, j.hom_inv_id_assoc y⟩⟩
  exact ⟨(ObjPull.pushEquiv h _).trans Ψ, fun σ => Category.id_comp _⟩

end

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
  {l l₂ : Level H} {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {s : S ⟶ Sp B}

theorem sabMap_lbIso {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem pushEquiv_act {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T : Over S')
    (c : 𝓞 E) (g : T ⟶ t'.G) :
    ObjPull.pushEquiv m.cart T (g ≫ t'.act.act c) = ObjPull.pushEquiv m.cart T g ≫ t.act.act c := by
  apply Over.OverMorphism.ext
  show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
  rw [Category.assoc, m.act, Category.assoc]

theorem levStr_of_obj (o : Obj D l b s) (T : Over S) (o' : Obj D l₂ b₂ (T.hom ≫ s)) (m : SABMap o'.t o.t T.hom)
    (hW : ∀ (T' : Over T.left) (k : ℤ) (x y : T' ⟶ o'.t.G) (x₀ y₀ : Over.mk (T'.hom ≫ T.hom) ⟶ o.t.G)
      (c : Γ(T'.left, ⊤)ˣ), x₀.left = x.left ≫ m.φ → y₀.left = y.left ≫ m.φ →
      (Out.WeilIs o'.t.G o'.t.PP.L k x y c ↔ Out.WeilIs o.t.G o.t.PP.L k x₀ y₀ c))
    (h1 : ∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m.φ = T.hom ≫ (o.eta a).left)
    (h2 : ∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = T.hom ≫ (o.etaA a).left) :
    ∃ χ θ : D.La → (T ⟶ o.t.G), LevStr o b₂ T χ θ ∧ (∀ a, (χ a).left = (o'.eta a).left ≫ m.φ) ∧
      ∀ a, (θ a).left = (o'.etaA a).left ≫ m.φ := by
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv m.cart
  refine ⟨fun a => Φ (o'.eta a), fun a => Φ (o'.etaA a), ⟨fun a c => ?_, fun a ha => ?_, fun a c => ?_, fun a => ?_,
    fun a => ?_, fun a => ?_, fun k _ _ x β hx y => ?_⟩, fun a => hΦ _, fun a => hΦ _⟩
  · simp only [o'.eta_add, map_mul]
  · simp only [o'.eta_ker a ha, map_one]
  · simp only [o'.etaA_add, map_mul]
  · simp only [o'.etaA_ker, map_one]
  · apply Over.OverMorphism.ext
    rw [← map_pow, hΦ, h1, Over.comp_left, ObjPull.toUnit_left']
  · apply Over.OverMorphism.ext
    rw [← map_pow, hΦ, h2, Over.comp_left, ObjPull.toUnit_left']
  · obtain ⟨x', rfl, rfl⟩ : ∃ (x' : Sp k ⟶ T.left) (h : x' ≫ T.hom = x), y = Over.homMk x' h :=
      ⟨y.left, Over.w y, rfl⟩
    obtain ⟨-, I, hI, hA, hM⟩ := o'.geom k x' β (by rw [← hx, Category.assoc])
    have key : ∀ σ : 𝟙_ (Over T.left) ⟶ o'.t.G, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ Φ σ =
        ObjPull.pushEquiv m.cart (Over.mk x') (toUnit _ ≫ σ) := fun σ => by
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, hΦ, ObjPull.toUnit_left', Category.assoc]
      rfl
    refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x')).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [MulEquiv.symm_apply_eq, pushEquiv_act, MulEquiv.apply_symm_apply]
    · exact (hW (Over.mk x') n _ _ g g' _ (ObjPull.pushEquiv_symm_left m.cart (Over.mk x') g).symm
        (ObjPull.pushEquiv_symm_left m.cart (Over.mk x') g').symm).1 hc
    · exact (key _).trans (congrArg _ (hA a))
    · exact (key _).trans (congrArg _ (hM a ha))

theorem obj_of_levStr (o : Obj D l b s) (hρ : b.ρ = b₂.ρ) (T : Over S) (t' : SAB H T.left) (m : SABMap t' o.t T.hom)
    (hW : ∀ (T' : Over T.left) (k : ℤ) (x y : T' ⟶ t'.G) (x₀ y₀ : Over.mk (T'.hom ≫ T.hom) ⟶ o.t.G)
      (c : Γ(T'.left, ⊤)ˣ), x₀.left = x.left ≫ m.φ → y₀.left = y.left ≫ m.φ →
      (Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs o.t.G o.t.PP.L k x₀ y₀ c))
    (hLie : ∀ (k : Type) [Field k] (x : Sp k ⟶ T.left) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act x τ n ↔ LieMult o.t.act (x ≫ T.hom) τ n)
    (hamp : Out.RelAmple t'.G t'.PP.L) (hk : Out.KTriv t'.G t'.PP.L)
    {χ θ : D.La → (T ⟶ o.t.G)} (h : LevStr o b₂ T χ θ) :
    ∃ (o' : Obj D l₂ b₂ (T.hom ≫ s)) (m' : SABMap o'.t o.t T.hom),
      ((∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = T.hom ≫ (o.eta a).left) ∧
        ∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = T.hom ≫ (o.etaA a).left) ∧
      (∀ a, (χ a).left = (o'.eta a).left ≫ m'.φ) ∧ ∀ a, (θ a).left = (o'.etaA a).left ≫ m'.φ := by
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv m.cart
  have hpr := o.proper
  refine ⟨{ t := t'
            proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
            ample := hamp
            ktriv := hk
            eta := fun a => Φ.symm (χ a)
            eta_add := fun a c => by rw [h.add, map_mul]
            eta_ker := fun a ha => by rw [h.ker a ha, map_one]
            etaA := fun a => Φ.symm (θ a)
            etaA_add := fun a c => by rw [h.addA, map_mul]
            etaA_ker := fun a => by rw [h.kerA a, map_one]
            geom := fun k _ _ x β hx => ?_ }, m, ⟨fun a => ?_, fun a => ?_⟩, fun a => ?_, fun a => ?_⟩
  · have hx' : (x ≫ T.hom) ≫ s = spMap β := by rw [← hx, Category.assoc]
    obtain ⟨hdet, -⟩ := o.geom k (x ≫ T.hom) β hx'
    obtain ⟨I, hI, hA, hM⟩ := h.geom k (x ≫ T.hom) β hx' (Over.homMk x rfl)
    rw [hρ] at hdet
    have key : ∀ σ : T ⟶ o.t.G, ObjPull.pushEquiv m.cart (Over.mk x) (toUnit _ ≫ Φ.symm σ) =
        (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ σ := fun σ => by
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, ← hΦ, ObjPull.toUnit_left',
        MulEquiv.apply_symm_apply]
      rfl
    refine ⟨fun τ => ?_, ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => pushEquiv_act m _ c g)
      (fun n g g' c hc => ?_) I, hI, fun a => ?_, fun a ha => ?_⟩
    · rw [hLie, hLie]
      exact hdet τ
    · exact (hW (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
    · exact (MulEquiv.eq_symm_apply _).2 ((key _).trans (hA a))
    · exact (MulEquiv.eq_symm_apply _).2 ((key _).trans (hM a ha))
  · refine (hΦ _).symm.trans ?_
    dsimp only
    rw [map_pow, MulEquiv.apply_symm_apply, h.low, Over.comp_left, ObjPull.toUnit_left']
  · refine (hΦ _).symm.trans ?_
    dsimp only
    rw [map_pow, MulEquiv.apply_symm_apply, h.lowA, Over.comp_left, ObjPull.toUnit_left']
  · exact ((hΦ _).symm.trans (by rw [MulEquiv.apply_symm_apply])).symm
  · exact ((hΦ _).symm.trans (by rw [MulEquiv.apply_symm_apply])).symm

theorem levelCover_field : Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G
    : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a
    : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act
    c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n
    : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G'
    : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L'
    : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull
    φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv
    G' L')) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
    : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n *
    m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ) (f
    : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (∀ a b, (N : ℤ) ∣ D.EF (f a) (f
    b) - ν * D.EF a b) → ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj
    G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ
    La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶
    G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a +
    c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a +
    c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a) → (∀ (S
    : Scheme.{0}) (P : Out.PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left,
    ⊤)ˣ), 0 < n → IsUnit (n : Γ(T.left,
    ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 → ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T'
    : Over S) (h : T' ⟶ T), Out.WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map
    (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (N : ℕ) (ν
    : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧ (l.A
    : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞
    E) D.La)) ∧ ∀ a, D.ModN l.A (g.f l.A a - a)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂
    : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂
    : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m
    : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫
    s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta
    a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA
    a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro _ hLie hAb hPol hSim hLift _ hTors hLoc hMult E _ _ _ H D l l₂ B _ b b₂ S s o hpq hl hρ hζ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l B b S s o
  obtain ⟨hfree, hfin⟩ := datum_free D
  let P : Out.PolAV S := ⟨o.t.G, hab, _, hsm, o.t.PP.L, o.t.PP.isLB, hrig, hsym, o.ample, o.ktriv⟩
  obtain ⟨V, χ, θ, hV1, hV2, hV3, hV, hext, hex⟩ := exists_levStr_rep o l₂ b₂ hl hζ (hSim E H D hpq).1
    (hLift E H D) (hMult E H D)
    (fun n hn => hTors S o.t.G n D.La hab (by
      have := (b.unit n hn).map (fnOn s)
      rwa [map_natCast] at this))
    (fun N hN T x y c hu hx hy hc => hLoc S P N T x y c hN hu hx hy hc)
  obtain ⟨t', ⟨m₀⟩⟩ : ∃ t' : SAB H V.left, Nonempty (SABMap t' o.t V.hom) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull V.hom o.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨-, hamp, hk⟩ := hAb _ _ o.t.G t'.G V.hom m₀.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB hab m₀.cart
    (sabMap_lbIso m₀)
  obtain ⟨o₂, m, hc, e1, e2⟩ := obj_of_levStr o hρ V t' m₀
    (weilIs_grpPullback_of_comm _ _ o.t.G t'.G V.hom m₀.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB m₀.cart (sabMap_lbIso m₀))
    (hLie _ _ _ o.t.G t'.G V.hom m₀.cm.F o.t.act t'.act m₀.cart m₀.act) (hamp o.ample) (hk o.ktriv) hV
  refine ⟨V.left, V.hom, o₂, m, hV1, hV2, hV3, hc, fun T f o' m' ⟨h1, h2⟩ => ?_⟩
  obtain ⟨χ', θ', hT, f1, f2⟩ := levStr_of_obj o (Over.mk f) o' m'
    (weilIs_grpPullback_of_comm _ _ o.t.G o'.t.G f m'.cm.F o.t.PP.L o'.t.PP.L o.t.PP.isLB o'.t.PP.isLB m'.cart (sabMap_lbIso m')) h1 h2
  obtain ⟨h, g1, g2⟩ := hex _ χ' θ' hT
  have huniq : ∀ h' : T ⟶ V.left, (h' ≫ V.hom = f ∧ ∃ u : ObjMap o' o₂ h', u.toSABMap.φ ≫ m.φ = m'.φ) →
      h' = h.left := by
    rintro h' ⟨hf, u, hu⟩
    refine congrArg CommaMorphism.left (hext (Over.mk f) (Over.homMk h' hf) h (fun a => ?_) fun a => ?_)
    · apply Over.OverMorphism.ext
      rw [g1, f1, Over.comp_left, e1, ← hu, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ m.φ) (u.eta a).symm
    · apply Over.OverMorphism.ext
      rw [g2, f2, Over.comp_left, e2, ← hu, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ m.φ) (u.etaA a).symm
  refine ⟨h.left, ⟨Over.w h, ?_⟩, huniq⟩
  obtain ⟨h', rfl, rfl⟩ : ∃ (h' : T ⟶ V.left) (e : h' ≫ V.hom = f), h = Over.homMk h' e := ⟨h.left, Over.w h, rfl⟩
  obtain ⟨u, hu⟩ := sabCancel pullCubCancel E H _ _ _ o.t o₂.t o'.t V.hom h' m m'
  have key : ∀ (σ' : 𝟙_ (Over T) ⟶ o'.t.G) (σ : 𝟙_ (Over V.left) ⟶ o₂.t.G),
      σ'.left ≫ m'.φ = h' ≫ σ.left ≫ m.φ → σ'.left ≫ u.cm.F = h' ≫ σ.left := fun σ' σ e => by
    apply m.cart.1.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (σ'.left ≫ ·) hu.symm).trans
        (e.trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, u.cart.1.w, ← Category.assoc, Over.w σ', Category.assoc, Over.w σ]
      simp
  refine ⟨⟨u, fun a => key _ _ ?_, fun a => key _ _ ?_⟩, hu.symm⟩
  · rw [← f1, ← e1, ← g1]
    rfl
  · rw [← f2, ← e2, ← g2]
    rfl

end GlobalTheory.LevCover
