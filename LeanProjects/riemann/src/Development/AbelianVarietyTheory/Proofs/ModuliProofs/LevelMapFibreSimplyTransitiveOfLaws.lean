import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

theorem objPull_of_lie_of_ample : (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro hLie hAb E _ _ _ H D l B B' _ _ b b' j S S' s s' f hρ hζ hs o
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' o.t f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f o.t
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := hAb S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  refine ⟨{ t := t'
            proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
            ample := hamp o.ample
            ktriv := hk o.ktriv
            eta := fun a => secPull m.cart (o.eta a)
            eta_add := fun a c => by rw [o.eta_add, map_mul]
            eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
            etaA := fun a => secPull m.cart (o.etaA a)
            etaA_add := fun a c => by rw [o.etaA_add, map_mul]
            etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨⟨m, fun a => secPull_left m.cart _, fun a => secPull_left m.cart _⟩⟩⟩
  obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) (β.comp j)
    (by rw [Category.assoc, hs, ← Category.assoc, hx, spMap_comp])
  rw [RingHom.comp_apply, hρ] at hdet
  rw [RingHom.comp_apply, hζ] at hI
  refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
    hI, fun a => ?_, fun a ha => ?_⟩
  · rw [hLie _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
      hLie _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB m.cart hL (Over.mk x) n g g'
      _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha))

end GlobalTheory.ObjPull

namespace GlobalTheory

theorem obj_rigid_of_laws : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _ m m' heta
  obtain ⟨hA, hd, hr, hs⟩ := hpol E H D l B' b' S' s' o'
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have hη : ∀ a, o'.eta a ≫ θ.hom = o'.eta a := fun a => by
    obtain ⟨σ, h₁, h₂⟩ := heta a
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans (h₁.trans h₂.symm)
    · rw [Over.w, Over.w]
  let P : Out.PolAV S' :=
    { A := o'.t.G, g := _, smoothDim := hd, L := o'.t.PP.L, isLB := o'.t.PP.isLB,
      ample := o'.ample, ktriv := o'.ktriv, isAb := hA, rigid := hr, sym := hs }
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMu : IsUnit (l.M : Γ(S', ⊤)) := by
    simpa using (b'.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ s'.appTop).hom
  have := hA.smooth
  have : Etale (Out.mulA o'.t.G l.M).left := GrpTangent.etale_id_pow o'.t.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL P l.M l.three_le θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric o'.t.G l.M θ.hom
        (obj_aut_fix_geometric_torsion o' θ hact ⟨w, hw⟩ hη))
    obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o'.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o'.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← hφ, h, Over.id_left, Category.id_comp]

end GlobalTheory

namespace GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Main

theorem exists_tate_push_comm
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

variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem exists_sim_of_fibre_comm
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo₂.X), ∃ o' : Obj D l₂ (baseKA l₂) (z ≫ Xo₂.s), Nonempty (ObjMap o' Xo₂.univ z))
    {k : Type} [Field k] [IsAlgClosed k]
    (hDiff : ∀ (z : Sp k ⟶ Xo.X) (I I' : TateIso D k (Over.mk z ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
      (fun n g g' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c))),
      ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hmA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (hLev : ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r)
    (x x' : Sp k ⟶ Xo₂.X) (hr : x ≫ r = x' ≫ r) (hs : x ≫ Xo₂.s = x' ≫ Xo₂.s) :
    ∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ x' = x ≫ ρ.hom := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, hIζ, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  obtain ⟨-, I', hIζ', hIA', hI'⟩ := Xo₂.univ.geom k x' β (hs.symm.trans hβ)
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨e', he'⟩ := exists_ptEquiv m.cart x' _ hr.symm
  obtain ⟨J, hJζ, hJ⟩ := exists_tate_push_comm m x _ rfl e he I
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push_comm m x' _ hr.symm e' he' I'
  obtain ⟨g, hg⟩ := hDiff _ J J'
  have key : ∀ (σ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (d : ℕ),
      (σ ^ d).left ≫ m.φ = r ≫ τ.left → e (toUnit _ ≫ σ) ^ d = e' (toUnit _ ≫ σ) ^ d := fun σ τ d h => by
    apply Over.OverMorphism.ext
    rw [← map_pow, ← map_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, he, he', unit_left, unit_left, Category.assoc,
      Category.assoc]
    exact (congrArg _ h).trans (((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.left) hr).trans
      (Category.assoc _ _ _))).trans (congrArg _ h.symm))
  obtain ⟨hin, hη⟩ := inGam_of_diff l l₂ hd J J' g hg
    (by rw [hJζ, hJζ']; exact Units.ext (hIζ'.trans hIζ.symm))
    (fun a => e (toUnit _ ≫ Xo₂.univ.eta a)) (fun a => e' (toUnit _ ≫ Xo₂.univ.eta a))
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [hJ, hI a ha]) (fun a ha => by rw [hJ', hI' a ha])
    (fun a => key _ _ _ (hm a)) (fun a => by rw [hJ, hJ', ← hIA, ← hIA']; exact key _ _ _ (hmA a))
  have hηA : ∀ a, e' (toUnit _ ≫ Xo₂.univ.etaA a) = e (toUnit _ ≫ Xo₂.univ.etaA (g.f l₂.A a)) := fun a => by
    rw [hIA, hIA', ← hJ, ← hJ', (hg _ l₂.A_pos).1]
  obtain ⟨ρ, hρ, hρr⟩ := hLev g hin
  refine ⟨g, ρ, hin, hρ, hρr, ?_⟩
  obtain ⟨hρs, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k x'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sab_cast hr.symm n₁
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m n₂
  obtain ⟨n₃, hn₃⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  have lev : ∀ (s : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (σ τ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G),
      s.left ≫ p.toSABMap.φ = x' ≫ σ.left → e' (toUnit _ ≫ σ) = e (toUnit _ ≫ τ) → τ.left ≫ ν.φ = ρ.hom ≫ σ.left →
      s.left ≫ n₃.φ = (x ≫ ρ.hom) ≫ σ.left := fun s σ τ h₁ h₂ h₃ => by
    have h₄ : s.left ≫ n.φ = x ≫ τ.left := by
      apply m.cart.1.hom_ext
      · have := congrArg (fun w => w.left) h₂
        simp only [he, he', unit_left] at this
        refine Eq.trans ?_ this
        rw [← h₁, Category.assoc, Category.assoc]
        exact congrArg _ (hn.symm.trans (hn₂.trans hn₁))
      · rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact (Category.id_comp x).trans (Category.comp_id x).symm
    rw [hn₃, ← Category.assoc, h₄, Category.assoc, Category.assoc]
    exact congrArg _ h₃
  obtain ⟨f, -, hf⟩ := Xo₂.rep (Sp k) (x' ≫ Xo₂.s) inferInstance o
  rw [hf x' ⟨rfl, ⟨p⟩⟩]
  refine (hf _ ⟨by rw [Category.assoc, hρs, hs], ⟨⟨n₃, fun a => ?_, fun a => ?_⟩⟩⟩).symm
  · exact lev _ _ _ (p.eta a) (hη a) (hν a)
  · exact lev _ _ _ (p.etaA a) (hηA a) (hνA a)

end Main

theorem levelMap_fibre_simply_transitive_of_laws :
    Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
        : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j
        : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
        : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
        o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b
        : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
        : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
        : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
        f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
        f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
        : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
        : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 *
        (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o
        : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M /
        l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨
        IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
        a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k
        : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
        : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
        n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
        : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
        : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
        n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
        a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
        : c.F = c₂.F) (rF
        : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
        hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
        : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
        : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ := by
  intro hL hPull _ hPol _ hRig _ hDiff _ hLev E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hm c c₂ hc rF hF₁ hF₂ k _ _ y y' hy
  have pull : ∀ (l : Level H) (Xo : Moduli D l) (k : Type) [Field k] (z : Sp k ⟶ Xo.X),
      ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z) := fun l Xo k _ z =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (z ≫ Xo.s) z rfl rfl
      (by rw [spMap_id', Category.comp_id]) Xo.univ
  constructor
  · have hr : (y ≫ pullback.fst _ _) ≫ r = (y' ≫ pullback.fst _ _) ≫ r := by
      rw [Category.assoc, Category.assoc, ← hF₁, ← Category.assoc, ← Category.assoc, hy]
    have hbij : Function.Bijective (IntermediateField.inclusion hc.le).toRingHom :=
      ⟨(IntermediateField.inclusion hc.le).toRingHom.injective, fun a => ⟨⟨a.1, hc.ge a.2⟩, rfl⟩⟩
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have hsnd : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ := by
      rw [← cancel_mono (spMap (IntermediateField.inclusion hc.le).toRingHom), Category.assoc, Category.assoc, ← hF₂,
        ← Category.assoc, ← Category.assoc, hy]
    have hs : (y ≫ pullback.fst _ _) ≫ Xo₂.s = (y' ≫ pullback.fst _ _) ≫ Xo₂.s := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, hsnd]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hPol E H D l _ (baseKA l) _ Xo.s Xo.univ
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
    have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
    let P : Out.PolAV Xo.X :=
      { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
        rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
    obtain ⟨g, ρ, a₁, a₂, a₃, a₄⟩ := exists_sim_of_fibre_comm (pull l₂ Xo₂) (k := k)
      (fun z => hDiff E H D k _ _ _ fun n p q a b _ hp hq ha hb =>
        unitOn_injective (((hL.weil _ P n (Over.mk z)).1 p q hp hq).unique ha hb))
      hd r m hm.2.2.1 hm.2.2.2 (hLev E H D l l₂ Xo Xo₂ hpq hd r jK m hm) _ _ hr hs
    exact ⟨g, ρ, a₁, a₂, a₃, a₄.trans (Category.assoc _ _ _)⟩
  · intro g ρ hg hρ hx
    exact trivAt_of_fixed (pull l Xo) (fun k _ z o' => hRig E H D l _ _ _ _ _ _ _ _ Xo.univ o' z (Or.inl inferInstance))
      hd r m hm.2.2.1 _ g ρ hg hρ ((Category.assoc _ _ _).trans hx)

end GlobalTheory.LevelFibre
