import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private lemma pullback_lift_clopen_immersion {W X Mη M P B B' Z : Scheme.{0}} (j : X ⟶ Mη) (f₁ : Mη ⟶ M) (f₂ : Mη ⟶ B') (s : M ⟶ B)
    (g : B' ⟶ B) (hp : IsPullback f₁ f₂ s g) (h : P ⟶ M) (w : W ⟶ X) (φ : W ⟶ P)
    (hc : IsPullback φ w h (j ≫ f₁)) (ε : Z ≅ W) (ρ : Z ⟶ P) (hρ : ρ = ε.hom ≫ φ) (t : Z ⟶ B')
    (ht : t = ε.hom ≫ w ≫ j ≫ f₂) (e : ρ ≫ h ≫ s = t ≫ g) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsOpenImmersion (pullback.lift ρ t e) ∧ IsClosedImmersion (pullback.lift ρ t e) := by
  have hQ : IsPullback (pullback.fst (h ≫ s) g) (pullback.snd (h ≫ s) g) (h ≫ s) g :=
    IsPullback.of_hasPullback _ _
  have hu0 : (pullback.fst (h ≫ s) g ≫ h) ≫ s = pullback.snd (h ≫ s) g ≫ g := by
    rw [Category.assoc]; exact pullback.condition
  let u : pullback (h ≫ s) g ⟶ Mη := hp.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) hu0
  have hu1 : u ≫ f₁ = pullback.fst _ _ ≫ h := hp.lift_fst _ _ _
  have hu2 : u ≫ f₂ = pullback.snd _ _ := hp.lift_snd _ _ _
  have A : IsPullback u (pullback.fst (h ≫ s) g) f₁ h :=
    IsPullback.of_right (h₁₂ := f₂) (v₁₃ := g) (h₂₂ := s) (by rw [hu2]; exact hQ.flip) hu1 hp.flip
  have hφ : φ ≫ h ≫ s = (w ≫ j ≫ f₂) ≫ g := by
    rw [← Category.assoc, hc.w]
    simp only [Category.assoc, hp.w]
  let l : W ⟶ pullback (h ≫ s) g := pullback.lift φ (w ≫ j ≫ f₂) hφ
  have hl1 : l ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd _ _ = w ≫ j ≫ f₂ := pullback.lift_snd _ _ _
  have hlu : l ≫ u = w ≫ j := by
    apply hp.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hl1, hc.w, Category.assoc]
    · rw [Category.assoc, hu2, hl2, Category.assoc]
  have B1 : IsPullback l w u j :=
    IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := h) (h₂₂ := f₁) (by rw [hl1]; exact hc) hlu A.flip
  have o1 : IsOpenImmersion l := MorphismProperty.of_isPullback (P := @IsOpenImmersion) B1.flip inferInstance
  have o2 : IsClosedImmersion l := MorphismProperty.of_isPullback (P := @IsClosedImmersion) B1.flip inferInstance
  have hE : pullback.lift ρ t e = ε.hom ≫ l := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hl1, hρ]
    · rw [pullback.lift_snd, Category.assoc, hl2, ht]
  rw [hE]
  exact ⟨inferInstance, inferInstance⟩

private lemma powMap_congr {S' S₁ : Scheme.{0}} {A' : Over S'} {A : Over S₁} {f f' : S' ⟶ S₁} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m = GlobalTheory.KS.powMap f' φ' h' m := by
  subst hf; subst hφ; rfl

theorem UpperTheory.tower_trivial_of_quotient_trace_powerCartesian :
    MIn → QObj → QComp → QIso → QUniq → TrEta → TrUnit → PowCart → PiZero := by
  intro hM hQO hQC hQI hQU hTE hTU hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hNum C
  haveI : IsNoetherianRing (Ow w) := inferInstance
  let N₀' : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  let β : Ow w →+* E := algebraMap (Ow w) E
  obtain ⟨j₀, hop, hcl, hj, φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ :=
    hM.cmp q (datAt S.atq S.sp) (Ow w) S.b E β gb S.mat.1 S.mat.2 S.N₀ S.std.three S.std.cop S.M (T.M N₀')
  let f₀ : (T.M N₀').X ⟶ S.M.X := j₀ ≫ pullback.fst _ _
  let n₀ : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N₀').univ S.M.univ f₀ 1 :=
    { φ := φA, φ₂ := φ₂, cart := hcart, sq := hsq, act := hact, pol := hpol,
      eta := fun y => by rw [one_smul]; exact heta y }
  let pw := GlobalTheory.KS.powMap f₀ n₀.φ n₀.cart.1.w k
  have pc := hPC _ _ _ (T.M N₀').univ.A S.M.univ.A S.M.univ.A f₀ (𝟙 _) n₀.φ (𝟙 _) n₀.cart.1.w (by simp) k
  have hs : f₀ ≫ S.M.s = (T.M N₀').s ≫ spMap β := by
    simp only [f₀, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hj]
  have hq : T.X.q (T.lev N₀') = (T.e N₀').hom ≫ (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom ≫ j₀ ≫ pullback.snd _ _ := by
    rw [hj, T.e_q]
  have e : ((T.e N₀').hom ≫ pw) ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s = T.X.q _ ≫ gen (Ow w) E := by
    rw [← T.e_q N₀']
    simp only [Category.assoc]
    rw [← Category.assoc pw, pc.2.1]
    simp only [Category.assoc]
    rw [hs]
  refine ⟨(T.e N₀').hom ≫ pw, e, ?_⟩
  haveI := hop
  haveI := hcl
  obtain ⟨h1, h2⟩ := pullback_lift_clopen_immersion j₀ (pullback.fst _ _) (pullback.snd _ _) S.M.s (spMap β)
    (IsPullback.of_hasPullback _ _) (GlobalTheory.KS.pow S.M.univ.A k).hom (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom pw
    (pc.1 n₀.cart.1) (T.e N₀') _ rfl _ hq e
  refine ⟨h1, h2, fun x y => ?_⟩
  obtain ⟨π, o, ψ, φ, hw, hπs, htrans, htr⟩ := T.tr_eq N N₀' 1 x y
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans (one_mem _)
  have heta' : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ ψ = o.eta (1 • y') := fun y' =>
    hTE p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans S.N₀ c 1 hNum.1 (_root_.mul_one _).symm y' y'
      ⟨0, zero_mem _, by simp⟩
  obtain ⟨n₁, hn₁⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ S.N₀ 1 _ _ _ (T.M N₀').s S.M.s S.M.s (T.M N₀').univ
    S.M.univ S.M.univ f₀ (𝟙 _)).2.2.2 _ (T.M N).s o π φ n₀
  obtain ⟨n₂, hn₂⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ N.1 S.N₀ 1 c _ _ (T.M N).s S.M.s (T.M N).univ o
    S.M.univ (π ≫ f₀) ψ hiso htrans.1 htrans.2.1 hlb heta' n₁
  obtain ⟨n₃, hn₃⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s S.Y.s S.M.s (T.M N).univ
    S.Y.univ S.M.univ C.j S.π).1 C.m S.mπ
  obtain ⟨o₀, ⟨n₄⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb β S.mat N.1 S.N₀ c hNum.1 (by have := N.2.1; omega)
    S.std.cop _ (T.M N).s (T.M N).univ
  obtain ⟨f', -, huniq⟩ := S.M.rep _ ((T.M N).s ≫ spMap β) o₀
  have key : ∀ (g : (T.M N).X ⟶ S.M.X), QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ g c →
      g ≫ S.M.s = (T.M N).s ≫ spMap β → g = f' := by
    intro g n hg
    have n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ (𝟙 _ ≫ g) c := by
      rw [Category.id_comp]; exact n
    obtain ⟨m, -⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s _ S.M.s (T.M N).univ
      o₀ S.M.univ (𝟙 _) g).2.2.1 inferInstance n₄ n'
    exact huniq g ⟨hg, ⟨m⟩⟩
  have hf : C.j ≫ S.π = π ≫ f₀ := by
    rw [key _ n₃ ?_, key _ n₂ ?_]
    · rw [Category.assoc, hs, ← Category.assoc, hπs]
    · rw [Category.assoc, S.ov, C.ov]
  have cast : ∀ {f f' : (T.M N).X ⟶ S.M.X} (_ : f = f')
      (n : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f c),
      ∃ n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f' c, n'.φ = n.φ := by
    intro f f' hff n
    subst hff
    exact ⟨n, rfl⟩
  obtain ⟨n₅, hn₅⟩ := cast hf n₃
  have hφ : C.m.φ ≫ S.mπ.φ = (ψ.left ≫ φ.φ) ≫ n₀.φ := by
    rw [← hn₃, ← hn₅, hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c S.std.three S.std.cop _ _ (T.M N).s S.M.s
      (T.M N).univ S.M.univ (π ≫ f₀) n₅ n₂, hn₂, hn₁, Category.assoc]
  have hv1 : ((ψ.left ≫ φ.φ) ≫ n₀.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ π ≫ f₀ := by
    rw [Category.assoc, n₀.cart.1.w, ← Category.assoc, hw, Category.assoc]
  have hv2 : (C.m.φ ≫ S.mπ.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ C.j ≫ S.π := by
    rw [Category.assoc, S.mπ.cart.1.w, ← Category.assoc, C.m.cart.1.w, Category.assoc]
  have c1 := (hPC _ _ _ (T.M N).univ.A (T.M N₀').univ.A S.M.univ.A π f₀ (ψ.left ≫ φ.φ) n₀.φ hw n₀.cart.1.w k).2.2 hv1
  have c2 := (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.M.univ.A C.j S.π C.m.φ S.mπ.φ C.m.cart.1.w S.mπ.cart.1.w k).2.2 hv2
  change T.X.tr (T.lev N) (T.lev N₀') 1 x y ≫ (T.e N₀').hom ≫ pw =
    ((T.e N).hom ≫ GlobalTheory.KS.powMap C.j C.m.φ C.m.cart.1.w k) ≫ GlobalTheory.KS.powMap S.π S.mπ.φ S.mπ.cart.1.w k
  rw [← Category.assoc, htr, Category.assoc, Category.assoc, c1, c2]
  exact congrArg _ (powMap_congr hf.symm hφ.symm hv1 hv2 k)
