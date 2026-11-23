import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProductStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

open CategoryTheory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => by
    have h1 := Xo.univ.eta_add (g a) (f a - g a)
    rwa [add_sub_cancel, Xo.univ.eta_ker _ (h a), _root_.mul_one] at h1
  unfold levR IsLevMove
  simp only [e]

end Rel

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_half (a : Dw.La) : ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ b = (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a := by
  have h : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  rw [map_add, show (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, zero_add]

theorem map_mem_smul_top {I : Ideal (𝓞 E)} (f : Dw.La →ₗ[𝓞 E] Dw.La) {a : Dw.La}
    (ha : a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have := l.three_le
  have h2 : l.M = 0 := by exact_mod_cast h1
  omega

theorem graph_iff {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) :
    (∀ q, φ (γ q) = Y.mulVec (φ q)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) → C a a' := by
  constructor
  · intro hg a ha a' ha' e
    rw [hC a ha a' ha', e, hg]
  · intro hg q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, e⟩ := exists_half (l := l) x
    have ha' := map_mem_smul_top (liftLa γ) ha
    rw [← e, ← liftLa_spec]
    exact (hC a ha _ ha').1 (hg a ha _ ha' (liftLa_spec _ a))

theorem sub_liftLa_mem {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (hγ : ∀ q, φ (γ q) = Y.mulVec (φ q)) (f : Dw.La →ₗ[𝓞 E] Dw.La)
    (hf : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a (f a)) (x : Dw.La) :
    f x - liftLa γ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨a, ha, e⟩ := exists_half (l := l) x
  have e1 := (hC a ha _ (map_mem_smul_top f ha)).1 (hf a ha)
  rw [← hγ, φ.injective.eq_iff, e, ← liftLa_spec] at e1
  have e2 : f x - f a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← map_sub]
    exact map_mem_smul_top f ((Submodule.Quotient.eq _).1 e.symm)
  have e3 := add_mem e2 ((Submodule.Quotient.eq _).1 e1)
  rwa [sub_add_sub_cancel] at e3

end Half

theorem exists_coord_of {O S La : Type} [CommRing O] [CommRing S] [AddCommGroup La] [Module O La] (o : O →+* S)
    {I J : Ideal O} {M r : ℕ} (hIJ : I * J = Ideal.span {(M : O)}) (hco : I ⊔ J = ⊤) (π : S →+* O ⧸ I)
    (hπ : ∀ a, π (o a) = Ideal.Quotient.mk I a) (hπ0 : ∀ s, π s = 0 ↔ s ∈ I.map o) (ρ : La →+ (Fin r → S))
    (hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a)
    (hsur : ∀ s : Fin r → S, ∃ (a : La) (s' : Fin r → S), s = ρ a + M • s')
    (hker : ∀ a : La, (∀ i, ρ a i ∈ I.map o) → a ∈ I • (⊤ : Submodule O La)) :
    ∃ φ : (La ⧸ (I • (⊤ : Submodule O La))) ≃ₗ[O] (Fin r → O ⧸ I), ∀ y : Matrix (Fin r) (Fin r) S,
      ∀ a ∈ J • (⊤ : Submodule O La), ∀ a' ∈ J • (⊤ : Submodule O La),
        (∃ s : Fin r → S, y.mulVec (ρ a) - ρ a' = M • s) ↔
          φ ((I • (⊤ : Submodule O La)).mkQ a') = (y.map π).mulVec (φ ((I • (⊤ : Submodule O La)).mkQ a)) := by
  have hMb : (M : O) ∈ I :=
    Ideal.mul_le_left (I := I) (J := J) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
  have hπM : ∀ s : S, π (M • s) = 0 := fun s => (hπ0 _).2 (by
    rw [nsmul_eq_mul, ← map_natCast o]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hMb))
  have hmem : ∀ K : Ideal O, ∀ a ∈ K • (⊤ : Submodule O La), ∀ i, ρ a i ∈ K.map o := fun K a ha i => by
    refine Submodule.smul_induction_on (p := fun a => ρ a i ∈ K.map o) ha ?_ ?_
    · intro b hb x _
      rw [hlin]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  let f : La →ₗ[O] (Fin r → O ⧸ I) :=
    { toFun := fun a i => π (ρ a i)
      map_add' := fun a b => funext fun i => by simp
      map_smul' := fun b a => funext fun i => by
        rw [hlin, Pi.smul_apply, smul_eq_mul, map_mul, hπ]
        rfl }
  have hk : LinearMap.ker f = I • (⊤ : Submodule O La) := by
    ext a
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hker a fun i => (hπ0 _).1 (congrFun h i), fun h => funext fun i => (hπ0 _).2 (hmem _ a h i)⟩
  have hs : Function.Surjective f := fun x => by
    choose b hb using fun i => Ideal.Quotient.mk_surjective (x i)
    obtain ⟨a, s', e⟩ := hsur fun i => o (b i)
    refine ⟨a, funext fun i => ?_⟩
    have := congrArg π (congrFun e i)
    rw [Pi.add_apply, map_add, Pi.smul_apply, hπM, add_zero, hπ, hb] at this
    exact this.symm
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs), fun y a ha a' ha' => ?_⟩
  change _ ↔ f a' = (y.map π).mulVec (f a)
  have hv : ∀ i, ((y.map π).mulVec (f a)) i = π (y.mulVec (ρ a) i) := fun i =>
    (RingHom.map_mulVec π y (ρ a) i).symm
  constructor
  · rintro ⟨s, e⟩
    funext i
    have := congrArg π (congrFun e i)
    rw [Pi.sub_apply, map_sub, Pi.smul_apply, hπM, sub_eq_zero] at this
    rw [hv]
    exact this.symm
  · intro e
    have h1 : ∀ i, (y.mulVec (ρ a) - ρ a') i ∈ Ideal.span {(M : S)} := fun i => by
      have hb : (y.mulVec (ρ a) - ρ a') i ∈ I.map o := by
        rw [← hπ0, Pi.sub_apply, map_sub, sub_eq_zero, ← hv, ← e]
        rfl
      have hc : (y.mulVec (ρ a) - ρ a') i ∈ J.map o := by
        refine sub_mem ?_ (hmem _ a' ha' i)
        exact Ideal.sum_mem _ (t := Finset.univ) (f := fun k => y i k * ρ a k) fun k _ =>
          Ideal.mul_mem_left _ _ (hmem _ a ha k)
      have hco' : I.map o ⊔ J.map o = ⊤ := by rw [← Ideal.map_sup, hco, Ideal.map_top]
      have hi := Submodule.mem_inf.2 ⟨hb, hc⟩
      rwa [← Ideal.mul_eq_inf_of_coprime hco', ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton,
        map_natCast] at hi
    choose s hs using fun i => Ideal.mem_span_singleton'.1 (h1 i)
    exact ⟨s, funext fun i => by rw [← hs i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩

theorem redAt_eq_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ}
    (β : GL (Fin r) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (w : Formalism.L2.DIV.Pl E) (hle : I ≤ w.asIdeal)
    (x : Formalism.L2.DIV.St β) (g : GL (Fin r) (Formalism.L2.DIV.kP w)) :
    Formalism.L2.DIV.redAt β w x = g ↔
      ((Formalism.L2.DIV.pullFr β x).1.map (resI F I hI)).map (Ideal.Quotient.factor hle) = g.1 := by
  rw [Units.ext_iff]
  refine Eq.congr_left ?_
  ext i k
  exact (factor_resI_eq_resS hI w hle _).symm

variable {D : D7}

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Cong (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (κ : GA D V) (a a' : Dw.La) : Prop :=
  ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w

set_option maxHeartbeats 800000 in

theorem exists_coord (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) :
    ∃ φ : LaMod Dw l ≃ₗ[𝓞 D.host.E] (Fin r → 𝓞 D.host.E ⧸ l.Mb),
      ∀ (κ : GA D V) (h : LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        Cong V ι l.M κ a a' ↔
          φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a') =
            ((Formalism.L2.DIV.pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec
              (φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a)) := by
  obtain ⟨ρ, hlin, hsur, hker, hcong⟩ := GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod D V r hr β hβ Dw.La ι hι l.M (by have := l.three_le; omega)
  obtain ⟨φ, hφ⟩ := exists_coord_of (Formalism.L2.DIV.oToS D.host.F D.host.E) l.prod l.coprime
    (resI D.host.F l.Mb (half_ne_bot l)) (resI_oToS _ _) (resI_eq_zero_iff _ _) ρ hlin hsur (hker _ _ l.prod)
  refine ⟨φ, fun κ h a ha a' ha' => ?_⟩
  have h1 := hcong κ _ (Formalism.L2.DIV.frGL_pullFr β ⟨_, h⟩).symm a a'
  have h2 := hφ (Formalism.L2.DIV.pullFr β ⟨_, h⟩).1 a ha a' ha'
  have h3 := h1.trans h2
  exact h3

theorem exists_groupEquiv (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hι : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hP : l.Mb = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) :
    ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l,
      (∀ g κ, LatticeBasisLifts.IsLift V hr β Pg g κ ↔
        LevelLiftConditions.IsLevLift l V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (ψ g) κ) ∧
      (∀ (K : Type) [Field K] (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) g,
        chiProd hle χ (LevelLiftConditions.levDet Dw l (ψ g)) = LatticeBasisLifts.chiDetG0 Pg r χ g) ∧
      (∀ g, LatticeBasisLifts.Induces Dw l V hr ι₀ β Pg g (liftLa (ψ g))) ∧
      ∀ g γ, (∃ κ, LatticeBasisLifts.IsLift V hr β Pg g κ) → LatticeBasisLifts.Induces Dw l V hr ι₀ β Pg g γ →
        ∀ a, γ a - liftLa (ψ g) a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  obtain ⟨φ, hφ⟩ := exists_coord l V hr β hβ _ hι
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.T.level_group_matrix_isomorphism D.host.E H Dw l Pg hP hle r φ
  have hred : ∀ (g : Formalism.L2.DIV.G0 Pg r) (x : Formalism.L2.DIV.St β),
      (∀ w : ↥Pg, Formalism.L2.DIV.redAt β w.1 x = g w) ↔
        ∀ q, φ (ψ g q) = ((Formalism.L2.DIV.pullFr β x).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec (φ q) := by
    intro g x
    have e1 := h1 g ((Formalism.L2.DIV.pullFr β x).1.map (resI D.host.F l.Mb (half_ne_bot l)))
    have e2 := fun w : ↥Pg => redAt_eq_iff β (half_ne_bot l) w.1 (hle w) x (g w)
    exact ⟨fun h => e1.2 fun w => (e2 w).1 (h w), fun h w => (e2 w).2 (e1.1 h w)⟩
  have hlift : ∀ g κ, LatticeBasisLifts.IsLift V hr β Pg g κ ↔
      LevelLiftConditions.IsLevLift l V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (ψ g) κ := by
    intro g κ
    have hst := GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral D V r hr β hβ κ
    have hgr := fun h => (hred g ⟨_, h⟩).trans (graph_iff φ _ _ (hφ κ h) (ψ g))
    exact and_congr_right fun _ =>
      ⟨fun ⟨h, hg⟩ => ⟨hst.2 h, (hgr h).1 hg⟩, fun ⟨h, hg⟩ => ⟨hst.1 h, (hgr (hst.1 h)).2 hg⟩⟩
  refine ⟨ψ, hlift, fun K _ χ g => ?_, fun g κ hκ a ha => ?_, fun g γ ⟨κ, hκ⟩ hγ => ?_⟩
  · rw [chiProd_apply, LatticeBasisLifts.chiDetG0_apply]
    exact Finset.prod_congr rfl fun w _ => congrArg (χ w) (h2 g w)
  · exact ((hlift g κ).1 hκ).2.2 a ha _ (map_mem_smul_top _ ha) (liftLa_spec _ a)
  · obtain ⟨h, hg⟩ := hκ.2
    have h3 := sub_liftLa_mem φ _ _ (hφ κ h) (ψ g) ((hred g ⟨_, h⟩).1 hg) γ
    exact h3 (hγ κ hκ)

theorem act_transport {Xo : Moduli Dw l} (c : Coeff l) {G : Type} [Group G] (ψ : G ≃* LevelLiftConditions.LevGrp Dw l)
    (γ : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La)
    (h : ∀ g a, γ g a - liftLa (ψ g) a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (∀ g, actLev (Xo := Xo) c (LatticeBasisLifts.levOf γ) g = actLev (Xo := Xo) c (levFull Dw l) (ψ g)) ∧
      (ActLev (Xo := Xo) c (LatticeBasisLifts.levOf γ) ↔ ActLev (Xo := Xo) c (levFull Dw l)) := by
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) g y y' ↔ levActR (Xo := Xo) (c := c) (levFull Dw l) (ψ g) y y' :=
    fun g S _ _ y y' => levR_congr (h g) y y'
  have key' : ∀ (g : LevelLiftConditions.LevGrp Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (levFull Dw l) g y y' ↔
        levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) (ψ.symm g) y y' := fun g S _ _ y y' => by
    rw [key, ψ.apply_symm_apply]
  refine ⟨fun g => ?_, fun L => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun L => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine LinearMap.ext fun f => funext fun p => funext fun y => ?_
    have e : (fun y' => levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) g y y') =
        fun y' => levActR (Xo := Xo) (c := c) (levFull Dw l) (ψ g) y y' := funext fun y' => propext (key g y y')
    have gen : ∀ P Q : FrPt Xo c p.R → Prop, P = Q → (open Classical in if h : ∃ y', P y' then h.choose else y) =
        (open Classical in if h : ∃ y', Q y' then h.choose else y) := fun P Q e => by subst e; rfl
    exact congrArg (f p) (gen _ _ e)
  · intro g S _ _ y
    simpa only [key'] using L.total (ψ.symm g) S y
  · intro g S _ _ y y' y'' a b
    exact L.func _ S y y' y'' ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro S _ _ y
    refine (key' 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g k S _ _ y y' y'' a b
    refine (key' _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat _ S T φ y y' z z' m ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor _ S t y y' z z' m ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S _ _ y
    simpa only [key] using L.total (ψ g) S y
  · intro g S _ _ y y' y'' a b
    exact L.func _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g k S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat _ S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor _ S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

end Dict

theorem readAd_eq (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c : (T.U j σ).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R j) (h : GA D (T.V j σ)) :
    LatticeBasisLifts.readAd T.toCore j σ c a f h = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * LevelLiftConditions.adFn T j σ c f h := rfl

theorem laws_iff (T : CoreJ D) (j : ℕ) (β : GL (Fin D.R.r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) (χ' : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ)
    (ψ : Formalism.L2.DIV.G0 Pg D.R.r ≃* LevelLiftConditions.LevGrp (T.Q.Dw j) T.Q.l)
    (hl : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) g κ, LatticeBasisLifts.IsLift (T.V j σ) hr β Pg g κ ↔
      LevelLiftConditions.IsLevLift T.Q.l (T.V j σ) (LevelLiftConditions.iotaAt T j σ hr) (ψ g) κ)
    (hχ : ∀ g, χ' (LevelLiftConditions.levDet _ _ (ψ g)) = LatticeBasisLifts.chiDetG0 Pg D.R.r χ g)
    (γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)
    (hγ : ∀ g a, γ g a - liftLa (ψ g) a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) :
    LatticeBasisLifts.LevelActionLaws T j β Pg χ γ ↔ LevelLiftConditions.GeoActAt T j χ' := by
  obtain ⟨h1, h2⟩ := act_transport (Xo := T.Q.Xo j) T.Q.c ψ γ hγ
  have hg : ∀ g, LatticeBasisLifts.geoAct T.toCore j γ g = LevelLiftConditions.geo T j (ψ g) := h1
  have h0 : ∀ a, (lieFac (T.Q.Dw j) (xiR D) a : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
  constructor
  · intro L
    refine ⟨h2.1 L.act, fun a n hd g => ?_, fun σ hσ hr g => ?_, fun σ hσ hr n hn => ?_, fun a n hd g => ?_⟩
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact hg g ▸ L.cusp a n hd g
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact (L.lift σ hσ hr g).imp fun κ => (hl σ hσ hr g κ).1
    · obtain ⟨c, hc, H⟩ := L.read σ hσ hr n hn
      refine ⟨c, hc, fun a hd f hf g κ hκ x => ?_⟩
      obtain ⟨g, rfl⟩ := ψ.surjective g
      have e := H a hd g κ ((hl σ hσ hr g κ).2 hκ) f hf x
      rw [readAd_eq, readAd_eq, hg, ← hχ, mul_left_comm] at e
      exact mul_left_cancel₀ (h0 a) e
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact hg g ▸ L.integral a n hd g
  · intro L
    refine ⟨h2.2 L.laws, fun a n hd g => ?_, fun σ hσ hr g => ?_, fun σ hσ hr n hn => ?_, fun a n hd g => ?_⟩
    · exact hg g ▸ L.keeps a n hd (ψ g)
    · exact (L.lifts σ hσ hr (ψ g)).imp fun κ => (hl σ hσ hr g κ).2
    · obtain ⟨c, hc, H⟩ := L.equiv σ hσ hr n hn
      refine ⟨c, hc, fun a hd g κ hκ f hf x => ?_⟩
      rw [readAd_eq, readAd_eq, hg, H a hd f hf (ψ g) κ ((hl σ hσ hr g κ).1 hκ) x, hχ, mul_left_comm]
    · exact hg g ▸ L.integral a n hd (ψ g)

theorem half_eq_prod {T : CoreJ D} (hT : LawsJ T) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) : T.Q.l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ Pg hPg
  have h := GlobalTheory.CoverHalf.squarefree_span_g D
  rw [← hT.pins.2.1.1, ← T.Q.l.prod] at h
  exact h.of_mul_left

theorem chiW_fixed {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    T.chiW j T.σ₀ x = 1 := by
  have h := (hT.muVal j hj T.σ₀ T.toCore.good_σ₀).2 1
  have hroot : ∀ y : (AE D)ˣ, cA D (y : AE D) = y → IsDetRoot (T.V j T.σ₀) 1 y := fun y hy => by
    unfold IsDetRoot
    rw [map_one, Units.val_one, Matrix.det_one, one_mul]
    exact hy.symm
  have e := (h x (hroot x hx)).symm.trans (h 1 (hroot 1 (by rw [Units.val_one, map_one])))
  rw [map_one] at e
  exact Circle.ext e

theorem isInvTame_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hle : ∀ w : ↥Pg, T.Q.l.Mb ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) :
    LatticeBasisLifts.IsInvTame T.toCore.σ₀ Pg (T.chiW j T.toCore.σ₀) χ ↔
      LevelLiftConditions.IsInvTame T.σ₀ T.Q.l.Mb (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) (T.chiW j T.σ₀)
        (chiProd hle χ) :=
  ⟨GlobalTheory.T.tame_product_character_inverse D T.Q.H T.Q.l Pg hle _ _ _ χ, GlobalTheory.T.tame_character_from_product D T.Q.H T.Q.l Pg hle _ _ _ χ (chiW_fixed hT hj)⟩

theorem conclusion_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (hr : (D.sp.W j).rank = D.R.r)
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) (β : GL (Fin D.R.r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis (D.sp.W j) hr β) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) :
    ((∀ g, ∃ γ₀, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g γ₀) ∧
      ∀ γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
        (∀ g, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g (γ g)) →
          LatticeBasisLifts.LevelActionLaws T j β Pg χ γ) ↔
      LevelLiftConditions.GeoActAt T j (chiProd (fun w => (hPg w.1).1 w.2) χ) := by
  have hV := hT.spaceW j hj
  have hι : LatEmb (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) := by
    obtain ⟨hr₀, -, -, -, -, -, -, h, -⟩ := hT.adPin j hj T.σ₀ T.toCore.good_σ₀
    have gen : ∀ (V : HSp D) (hV : V.rank = D.R.r), V = D.sp.W j →
        LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hV) ∘ₗ T.iota j) →
        LatEmb (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) := by
      rintro V _ rfl h
      exact h
    exact gen _ hr₀ (hV _ T.toCore.good_σ₀) h
  obtain ⟨ψ, h1, h2, h3, h4⟩ := exists_groupEquiv T.Q.l (D.sp.W j) hr β hβ (T.iota j) hι Pg (half_eq_prod hT hPg)
    (fun w => (hPg w.1).1 w.2)
  have gen : ∀ (V : HSp D) (hV : V.rank = D.R.r), V = D.sp.W j →
      (∀ g κ, LatticeBasisLifts.IsLift V hV β Pg g κ ↔ LevelLiftConditions.IsLevLift T.Q.l V
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hV) ∘ₗ T.iota j) (ψ g) κ) ∧
      ∀ g, (∃ κ, LatticeBasisLifts.IsLift V hV β Pg g κ) → ∃ κ, LatticeBasisLifts.IsLift (D.sp.W j) hr β Pg g κ := by
    rintro V _ rfl
    exact ⟨h1, fun _ h => h⟩
  have hiff := laws_iff T j β Pg χ _ ψ (fun σ hσ hr' => (gen _ hr' (hV σ hσ)).1) (h2 _ χ)
  constructor
  · rintro ⟨-, H⟩
    exact (hiff _ fun g a => by rw [sub_self]; exact zero_mem _).1 (H (fun g => liftLa (ψ g)) h3)
  · intro L
    refine ⟨fun g => ⟨_, h3 g⟩, fun γ hγ => (hiff γ fun g => h4 g _ ?_ (hγ g)).2 L⟩
    have hr₀ : (T.V j T.σ₀).rank = D.R.r := by rw [hV _ T.toCore.good_σ₀]; exact hr
    have G := gen _ hr₀ (hV _ T.toCore.good_σ₀)
    exact G.2 g ((L.lifts T.σ₀ T.toCore.good_σ₀ hr₀ (ψ g)).imp fun κ => (G.1 g κ).2)

theorem at_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) :
    (∀ (hr : (D.sp.W j).rank = D.R.r) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)),
      (∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) →
      ∀ β : GL (Fin D.R.r) (EAf D), LatticeBasisLifts.IsLatBasis (D.sp.W j) hr β →
      ∀ χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ,
        LatticeBasisLifts.IsInvTame T.toCore.σ₀ Pg (T.chiW j T.toCore.σ₀) χ →
        (∀ g, ∃ γ₀, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g γ₀) ∧
        ∀ γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
          (∀ g, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g (γ g)) →
            LatticeBasisLifts.LevelActionLaws T j β Pg χ γ) ↔
    ∀ χ : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ,
      LevelLiftConditions.IsInvTame T.σ₀ T.Q.l.Mb (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) (T.chiW j T.σ₀) χ →
        LevelLiftConditions.GeoActAt T j χ := by
  constructor
  · intro H χ' hχ'
    have hr : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2
    obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_lattice_basis_hermitian_space D (D.sp.W j) _ hr
    let Pg := (Ideal.finite_factors (I := T.Q.l.Mb) (half_ne_bot T.Q.l)).toFinset
    have hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal := fun w => by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le
    obtain ⟨χ, rfl⟩ := exists_chiProd_eq (half_eq_prod hT hPg) (fun w => (hPg w.1).1 w.2) χ'
    exact (conclusion_iff hT hj hr hPg β hβ χ).1 (H hr Pg hPg β hβ χ ((isInvTame_iff hT hj _ χ).2 hχ'))
  · intro H hr Pg hPg β hβ χ hχ
    exact (conclusion_iff hT hj hr hPg β hβ χ).2 (H _ ((isInvTame_iff hT hj _ χ).1 hχ))

theorem geoLevelAction_iff_geoAct : LatticeBasisLifts.GeoLevelAction ↔ LevelLiftConditions.GeoAct :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hT => forall_congr' fun _ => forall_congr' fun hj =>
    at_iff hT hj

end GlobalTheory.GeoActCompare
