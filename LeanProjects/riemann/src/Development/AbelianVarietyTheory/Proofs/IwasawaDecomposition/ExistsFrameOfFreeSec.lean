import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open GlobalTheory.FramePull GlobalTheory.ConstFam

theorem exists_sabPull {S S' : Scheme.{0}} (f : S' ⟶ S)
    (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_trait_map {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}} {t : SAB H (Sp R)} {tC : SAB H Z}
    {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z} (hu : IsProper u.G.hom) (aT : SABMap u t (jK R))
    (aC : SABMap u tC x) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hg : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r))
    (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) :
    ∃ (Dd : SAB H (Sp (FractionRing W))) (tW : SAB H (Sp W)) (c0 : SABMap Dd u (spMap gam)) (mm : SABMap Dd tW (jK W))
      (a1 : SABMap tW t (spMap φ)) (a3 : SABMap tW tC χ), IsProper Dd.G.hom ∧
      c0.φ ≫ aT.φ = mm.φ ≫ a1.φ ∧ c0.φ ≫ aC.φ = mm.φ ≫ a3.φ := by
  have := hW.1
  obtain ⟨Dd, ⟨c0⟩⟩ := exists_sabPull (spMap gam) u
  obtain ⟨tW, ⟨a1⟩⟩ := exists_sabPull (spMap φ) t
  obtain ⟨tW', ⟨a2⟩⟩ := exists_sabPull χ tC
  obtain ⟨n₁, e₁⟩ := LevelCover.sab_comp c0 aT (e := jK W ≫ spMap φ) (ArcExtends.spMap_jK hg)
  obtain ⟨mm, e₂⟩ := LevelCover.sab_cancel a1 n₁ (jK W) rfl
  obtain ⟨n₂, e₃⟩ := LevelCover.sab_comp c0 aC (e := jK W ≫ χ) h
  obtain ⟨mm', e₄⟩ := LevelCover.sab_cancel a2 n₂ (jK W) rfl
  have hD : IsProper Dd.G.hom := MorphismProperty.of_isPullback (P := @IsProper) c0.cart.1 hu
  obtain ⟨ψ, hψ⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H W hW.2.1 tW tW' Dd hD mm mm'
  obtain ⟨a3, e₅⟩ := LevelCover.sab_comp ψ a2 (e := χ) (Category.id_comp _)
  refine ⟨Dd, tW, c0, mm, a1, a3, hD, by rw [e₂, e₁], ?_⟩
  rw [e₅, ← Category.assoc, hψ, e₄, e₃]

def RW {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : Prop :=
  PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e

theorem exists_rw {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) : ∃ w, RW m w := by
  obtain ⟨w, g, r, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
  exact ⟨w, g, r⟩

theorem exists_comp_rw {S₀ S₁ S : Scheme.{0}} {D : SAB H S₀} {t₁ : SAB H S₁} {t : SAB H S} {f : S₀ ⟶ S₁} {g : S₁ ⟶ S}
    (c : SABMap D t₁ f) (a : SABMap t₁ t g) {wc wa} (rc : RW c wc) (ra : RW a wa) {Φ : D.G.left ⟶ t.G.left}
    (e : c.φ ≫ a.φ = Φ) : ∃ w : LB.Iso D.PP.L (t.PP.L.pull Φ), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec D.G) (fun _ => eSec t.G) (fun _ => 1) D.PP.rig t.PP.rig (c.cm.e ≫ a.cm.e) ∧
      ∀ (Y : Scheme.{0}) (ρ : Y ⟶ D.G.left) (y : Y) (j : t.PP.L.ι) (i : t₁.PP.L.ι) (k : D.PP.L.ι),
        a.φ (c.φ (ρ y)) ∈ t.PP.L.U j → c.φ (ρ y) ∈ t₁.PP.L.U i → ρ y ∈ D.PP.L.U k →
        gw w ρ y j k = gw wa (ρ ≫ c.φ) y j i * gw wc ρ y i k := by
  subst e
  obtain ⟨w, T⟩ := exists_comp t₁.PP.isLB wa wc ra.1 rc.1 t.PP.isLB D.PP.isLB
  exact ⟨w, T.pgen_comp t₁.PP.isLB ra.1 rc.1, T.pmaps_comp t₁.PP.isLB (fun _ => c.cm.e_comm) ra.2 rc.2, T⟩

theorem gw_tri_eq (hG : GlobalFnsSt) {S₀ S₁ S₂ S : Scheme.{0}} {D : SAB H S₀} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {t : SAB H S}
    {f₁ : S₀ ⟶ S₁} {f₂ : S₀ ⟶ S₂} {g₁ : S₁ ⟶ S} {g₂ : S₂ ⟶ S} (hD : IsProper D.G.hom) (c₁ : SABMap D t₁ f₁)
    (c₂ : SABMap D t₂ f₂) (a₁ : SABMap t₁ t g₁) (a₂ : SABMap t₂ t g₂) (hφ : c₁.φ ≫ a₁.φ = c₂.φ ≫ a₂.φ)
    (hb : f₁ ≫ g₁ = f₂ ≫ g₂) {wc₁ wc₂ wa₁ wa₂} (rc₁ : RW c₁ wc₁) (rc₂ : RW c₂ wc₂) (ra₁ : RW a₁ wa₁) (ra₂ : RW a₂ wa₂)
    (Y : Scheme.{0}) (ρ : Y ⟶ D.G.left) (y : Y) (j : t.PP.L.ι) (i₁ : t₁.PP.L.ι) (i₂ : t₂.PP.L.ι) (k : D.PP.L.ι)
    (hj : a₁.φ (c₁.φ (ρ y)) ∈ t.PP.L.U j) (hj₂ : a₂.φ (c₂.φ (ρ y)) ∈ t.PP.L.U j) (h₁ : c₁.φ (ρ y) ∈ t₁.PP.L.U i₁)
    (h₂ : c₂.φ (ρ y) ∈ t₂.PP.L.U i₂) (hk : ρ y ∈ D.PP.L.U k) :
    gw wa₁ (ρ ≫ c₁.φ) y j i₁ * gw wc₁ ρ y i₁ k = gw wa₂ (ρ ≫ c₂.φ) y j i₂ * gw wc₂ ρ y i₂ k := by
  obtain ⟨W₁, g₁', p₁, T₁⟩ := exists_comp_rw c₁ a₁ rc₁ ra₁ rfl
  obtain ⟨W₂, g₂', p₂, T₂⟩ := exists_comp_rw c₂ a₂ rc₂ ra₂ hφ.symm
  have he : c₂.cm.e ≫ a₂.cm.e = c₁.cm.e ≫ a₁.cm.e := by
    rw [c₁.base, c₂.base, a₁.base, a₂.base]; exact hb.symm
  rw [he] at p₂
  have he' : eSec D.G ≫ c₁.φ ≫ a₁.φ = (c₁.cm.e ≫ a₁.cm.e) ≫ eSec t.G := by
    rw [← Category.assoc, c₁.cm.e_comm, Category.assoc, a₁.cm.e_comm, Category.assoc]
  have m₁ := (maps_iff W₁ _ (fun _ : PUnit => eSec t.G) _ D.PP.rig t.PP.rig (c₁.cm.e ≫ a₁.cm.e)
    (rigPullOf _ _ he' t.PP.L t.PP.rig) (rigPull_le _ _ he' t.PP.L) (fun _ => rfl)).2 p₁
  have m₂ := (maps_iff W₂ _ (fun _ : PUnit => eSec t.G) _ D.PP.rig t.PP.rig (c₁.cm.e ≫ a₁.cm.e)
    (rigPullOf _ _ he' t.PP.L t.PP.rig) (rigPull_le _ _ he' t.PP.L) (fun _ => rfl)).2 p₂
  have hA : IsAbelianScheme D.G := AbelianSchemeGerms.isAbelianScheme_of_proper D.G D.semi
  have e : W₁ = W₂ := iso_unique_of_rig hG D.G hA D.PP.isLB t.PP.isLB ((isGen_iff _).2 g₁') ((isGen_iff _).2 g₂') m₁ m₂
  subst e
  rw [← T₁ Y ρ y j i₁ k hj h₁ hk, ← T₂ Y ρ y j i₂ k hj₂ h₂ hk]

section Move

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

theorem exists_thr_iso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {T : Over Z} {T₀ : Over S}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} [IsIso Φ] (hΦ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F)
    (a : LB.Sec (LPow G L (N : ℤ) T)) : ∃ t, TransportedAlt w Φ a t :=
  exists_thr_up hw hL₀ hL (Ψ := inv Φ) (by rw [← hΦ, IsIso.inv_hom_id_assoc]) (IsIso.hom_inv_id _) a

theorem exists_iso_cmp (hF : IsPullback F G.hom G₀.hom π) {V : Scheme.{0}} (a : V ⟶ Z) (a₀ : V ⟶ S) (e : a ≫ π = a₀) :
    ∃ Φ : (Over.mk a ⊗ G).left ⟶ (Over.mk a₀ ⊗ G₀).left, IsIso Φ ∧
      Φ ≫ (fst (Over.mk a₀) G₀).left = (fst (Over.mk a) G).left ≫ 𝟙 V ∧
      Φ ≫ (snd (Over.mk a₀) G₀).left = (snd (Over.mk a) G).left ≫ F := by
  have hu : (Iso.refl V).hom ≫ (Over.mk a₀).hom = (Over.mk a).hom ≫ π := (Category.id_comp _).trans e.symm
  exact ⟨SecMove.totMap hF (T' := Over.mk a) (T := Over.mk a₀) (Iso.refl V) hu, SecMove.totMap_isIso hF _ hu,
    SecMove.totMap_fst hF _ hu, SecMove.totMap_snd hF _ hu⟩

theorem lin_thr_iff (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}} {χ : V ⟶ Z} {χ₀ : V ⟶ S} {T : Over Z} {T₀ : Over S}
    {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀} {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left}
    {Φ' : (Over.mk χ ⊗ G).left ⟶ (Over.mk χ₀ ⊗ G₀).left} [IsIso Φ']
    (a₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left ≫ 𝟙 V)
    (hc : Φ' ≫ (h₀ ▷ G₀).left = (h ▷ G).left ≫ Φ) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)} (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i))
    {s : LB.Sec (LPow G L (N : ℤ) (Over.mk χ))} {s₀ : LB.Sec (LPow G₀ L₀ (N : ℤ) (Over.mk χ₀))} (hs : TransportedAlt w Φ' s s₀)
    (c : Fin n → Γ(V, ⊤)) : Lin G₀ L₀ N h₀ b₀ c s₀ ↔ Lin G L N h b c s := by
  have a₁' : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left := a₁.trans (Category.comp_id _)
  rw [lin_iff, lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ') z J₀ hJ₀
    rw [Category.assoc r Φ' (fst (Over.mk χ₀) G₀).left, a₁'] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ inv Φ') z hJ₀ hJ _).2 (H W (r ≫ inv Φ') z J hJ)
    have e : (r ≫ inv Φ') ≫ (fst (Over.mk χ) G).left = r ≫ (fst (Over.mk χ₀) G₀).left := by
      rw [← a₁', Category.assoc, IsIso.inv_hom_id_assoc]
    rw [Category.assoc r (inv Φ') Φ', IsIso.inv_hom_id, Category.comp_id, e] at this
    exact this

theorem basis_thr_iff (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}} {χ : V ⟶ Z} {χ₀ : V ⟶ S} {T : Over Z}
    {T₀ : Over S} {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀} {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left}
    {Φ' : (Over.mk χ ⊗ G).left ⟶ (Over.mk χ₀ ⊗ G₀).left} [IsIso Φ']
    (a₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left ≫ 𝟙 V)
    (a₂ : Φ' ≫ (snd (Over.mk χ₀) G₀).left = (snd (Over.mk χ) G).left ≫ F)
    (hc : Φ' ≫ (h₀ ▷ G₀).left = (h ▷ G).left ≫ Φ) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)} (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) :
    BasisAlong G₀ L₀ N h₀ b₀ ↔ BasisAlong G L N h b := by
  constructor
  · intro H s
    obtain ⟨s₀, hs⟩ := exists_thr_iso hw hL₀ hL a₂ s
    exact (existsUnique_congr fun c => lin_thr_iff hL₀ hL a₁ hc hb hs c).1 (H s₀)
  · intro H s₀
    obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL a₂ s₀
    exact (existsUnique_congr fun c => lin_thr_iff hL₀ hL a₁ hc hb hs c).2 (H s)

end Move

theorem lin_one_of {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ} {T T' : Over S} {h : T' ⟶ T}
    {b : LB.Sec (LPow G L (N : ℤ) T)} {s : LB.Sec (LPow G L (N : ℤ) T')}
    (H : ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good L z J →
      FramePull.sv s r z J = FramePull.sv b (r ≫ (h ▷ G).left) z J) : Lin G L N h (fun _ : Fin 1 => b) (fun _ => 1) s := by
  rw [lin_iff]
  intro W r z J hJ
  rw [H W r z J hJ, Fin.sum_univ_one, gs_one, _root_.one_mul]

theorem exists_pt {S : Scheme.{0}} {G : Over S} (T : Over S) {Y : Scheme.{0}} (a : Y ⟶ T.left) (b : Y ⟶ G.left)
    (h : a ≫ T.hom = b ≫ G.hom) : ∃ ρ : Y ⟶ (T ⊗ G).left, ρ ≫ (fst T G).left = a ∧ ρ ≫ (snd T G).left = b :=
  ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem value_eq (hG : GlobalFnsSt) {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] {Z : Scheme.{0}}
    {t : SAB H (Sp R)} {tC : SAB H Z} {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z}
    {Dd : SAB H (Sp (FractionRing W))} {tW : SAB H (Sp W)} {φ : R →+* W} {gam : FractionRing R →+* FractionRing W}
    {χ : Sp W ⟶ Z} (h : spMap gam ≫ x = jK W ≫ χ) (hsq : spMap gam ≫ jK R = jK W ≫ spMap φ)
    (hD : IsProper Dd.G.hom) {aT : SABMap u t (jK R)} {aC : SABMap u tC x} {c0 : SABMap Dd u (spMap gam)}
    {mm : SABMap Dd tW (jK W)} {a1 : SABMap tW t (spMap φ)} {a3 : SABMap tW tC χ}
    (e₁ : c0.φ ≫ aT.φ = mm.φ ≫ a1.φ) (e₂ : c0.φ ≫ aC.φ = mm.φ ≫ a3.φ) {wT wC w0 wm w1 w3}
    (rT : RW aT wT) (rC : RW aC wC) (r0 : RW c0 w0) (rm : RW mm wm) (r1 : RW a1 w1) (r3 : RW a3 w3) {N : ℕ}
    {ΦR : (Over.mk (𝟙 (Sp (FractionRing R))) ⊗ u.G).left ⟶ (Over.mk (𝟙 (Sp R)) ⊗ t.G).left}
    {Φx : (Over.mk (𝟙 (Sp (FractionRing R))) ⊗ u.G).left ⟶ (Over.mk x ⊗ tC.G).left}
    {Φ1 : (Over.mk (𝟙 (Sp W)) ⊗ tW.G).left ⟶ (Over.mk (𝟙 (Sp R)) ⊗ t.G).left}
    {Φ3 : (Over.mk (𝟙 (Sp W)) ⊗ tW.G).left ⟶ (Over.mk χ ⊗ tC.G).left}
    (a₁ : ΦR ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = (fst (Over.mk (𝟙 (Sp (FractionRing R)))) u.G).left ≫ jK R)
    (a₂ : ΦR ≫ (snd (Over.mk (𝟙 (Sp R))) t.G).left = (snd (Over.mk (𝟙 (Sp (FractionRing R)))) u.G).left ≫ aT.φ)
    (x₁ : Φx ≫ (fst (Over.mk x) tC.G).left = (fst (Over.mk (𝟙 (Sp (FractionRing R)))) u.G).left ≫ 𝟙 _)
    (x₂ : Φx ≫ (snd (Over.mk x) tC.G).left = (snd (Over.mk (𝟙 (Sp (FractionRing R)))) u.G).left ≫ aC.φ)
    (p₁ : Φ1 ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = (fst (Over.mk (𝟙 (Sp W))) tW.G).left ≫ spMap φ)
    (p₂ : Φ1 ≫ (snd (Over.mk (𝟙 (Sp R))) t.G).left = (snd (Over.mk (𝟙 (Sp W))) tW.G).left ≫ a1.φ)
    (s₁ : Φ3 ≫ (fst (Over.mk χ) tC.G).left = (fst (Over.mk (𝟙 (Sp W))) tW.G).left ≫ 𝟙 _)
    (s₂ : Φ3 ≫ (snd (Over.mk χ) tC.G).left = (snd (Over.mk (𝟙 (Sp W))) tW.G).left ≫ a3.φ)
    {a : LB.Sec (LPow u.G u.PP.L (N : ℤ) (Over.mk (𝟙 _)))} {b : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 _)))}
    {c : LB.Sec (LPow tW.G tW.PP.L (N : ℤ) (Over.mk (𝟙 _)))} {f : LB.Sec (LPow tC.G tC.PP.L (N : ℤ) (Over.mk x))}
    {b' : LB.Sec (LPow tC.G tC.PP.L (N : ℤ) (Over.mk χ))} (hA : TransportedAlt wT ΦR a b) (hf : TransportedAlt wC Φx a f) (hc : TransportedAlt w1 Φ1 c b)
    (hb' : TransportedAlt w3 Φ3 c b') {Y : Scheme.{0}} (r : Y ⟶ (Over.mk (jK W ≫ χ) ⊗ tC.G).left) (z : Y) {J}
    (hJ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good tC.PP.L z J) :
    FramePull.sv f (r ≫ ((Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) ▷ tC.G).left) z J =
      FramePull.sv b' (r ≫ ((Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) ▷ tC.G).left) z J := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp mm a3 (e := jK W ≫ χ) rfl
  have wp : (r ≫ (snd (Over.mk (jK W ≫ χ)) tC.G).left) ≫ tC.G.hom = (r ≫ (fst (Over.mk (jK W ≫ χ)) tC.G).left) ≫ jK W ≫ χ := by
    rw [Category.assoc, Category.assoc, Frames.snd_hom]; rfl
  obtain ⟨ρ, ρ₁, ρ₂⟩ : ∃ ρ : Y ⟶ Dd.G.left, ρ ≫ n.φ = r ≫ (snd (Over.mk (jK W ≫ χ)) tC.G).left ∧
      ρ ≫ Dd.G.hom = r ≫ (fst (Over.mk (jK W ≫ χ)) tC.G).left :=
    ⟨n.cart.1.lift _ _ wp, n.cart.1.lift_fst _ _ wp, n.cart.1.lift_snd _ _ wp⟩
  rw [hn] at ρ₁
  obtain ⟨ρu, u₁, u₂⟩ := exists_pt (Over.mk (𝟙 (Sp (FractionRing R)))) (G := u.G) (ρ ≫ Dd.G.hom ≫ spMap gam) (ρ ≫ c0.φ) (by
    show (_ ≫ _) ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, c0.cart.1.w])
  obtain ⟨ρw, v₁, v₂⟩ := exists_pt (Over.mk (𝟙 (Sp W))) (G := tW.G) (ρ ≫ Dd.G.hom ≫ jK W) (ρ ≫ mm.φ) (by
    show (_ ≫ _) ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, mm.cart.1.w])
  have F₁ : ρu ≫ Φx = r ≫ ((Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) ▷ tC.G).left := by
    apply prod_ext
    · rw [Category.assoc, x₁, Category.comp_id, u₁, Category.assoc, FrameGen.wh_fst, ← Category.assoc, ← Category.assoc, ← ρ₂]
      simp
    · rw [Category.assoc, x₂, reassoc_of% u₂, Category.assoc, FrameGen.wh_snd, e₂, ρ₁]
  have F₂ : ρw ≫ Φ3 = r ≫ ((Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) ▷ tC.G).left := by
    apply prod_ext
    · rw [Category.assoc, s₁, Category.comp_id, v₁, Category.assoc, FrameGen.wh_fst, ← Category.assoc, ← Category.assoc, ← ρ₂]
      simp
    · rw [Category.assoc, s₂, reassoc_of% v₂, Category.assoc, FrameGen.wh_snd, ρ₁]
  have F₃ : ρu ≫ ΦR = ρw ≫ Φ1 := by
    apply prod_ext
    · rw [Category.assoc, Category.assoc, a₁, p₁, reassoc_of% u₁, reassoc_of% v₁, hsq]
    · rw [Category.assoc, Category.assoc, a₂, p₂, reassoc_of% u₂, reassoc_of% v₂, e₁]
  obtain ⟨Ju, hJu⟩ := exists_good' u.PP.isLB z
  obtain ⟨Jw, hJw⟩ := exists_good' tW.PP.isLB z
  obtain ⟨Jt, hJt⟩ := exists_good' t.PP.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good' Dd.PP.isLB z
  have E₁ := hf Y ρu z J Ju hJ hJu
  have E₂ := hA Y ρu z Jt Ju hJt hJu
  have E₃ := hb' Y ρw z J Jw hJ hJw
  have E₄ := hc Y ρw z Jt Jw hJt hJw
  rw [u₂] at E₁ E₂
  rw [v₂] at E₃ E₄
  rw [F₁] at E₁
  rw [F₂] at E₃
  rw [F₃, E₄] at E₂
  rw [E₁, E₃]
  have q₁ : (ρ ≫ c0.φ) ≫ aC.φ = (ρ ≫ mm.φ) ≫ a3.φ := by rw [Category.assoc, Category.assoc, e₂]
  have q₂ : (ρ ≫ c0.φ) ≫ aT.φ = (ρ ≫ mm.φ) ≫ a1.φ := by rw [Category.assoc, Category.assoc, e₁]
  have m₁ : ((ρ ≫ mm.φ) ≫ a3.φ) z ∈ tC.PP.L.U (J ((ρ ≫ c0.φ) ≫ aC.φ)) := by rw [← q₁]; exact hJ _
  have m₂ : ((ρ ≫ mm.φ) ≫ a1.φ) z ∈ t.PP.L.U (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) := by rw [← q₂]; exact hJt _
  have T₁ := gw_tri_eq hG hD c0 mm aC a3 e₂ h r0 rm rC r3 Y ρ z (J ((ρ ≫ c0.φ) ≫ aC.φ)) (Ju (ρ ≫ c0.φ))
    (Jw (ρ ≫ mm.φ)) (J₀ ρ) (hJ ((ρ ≫ c0.φ) ≫ aC.φ)) m₁ (hJu _) (hJw _) (hJ₀ _)
  have T₂ := gw_tri_eq hG hD c0 mm aT a1 e₁ hsq r0 rm rT r1 Y ρ z (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) (Ju (ρ ≫ c0.φ))
    (Jw (ρ ≫ mm.φ)) (J₀ ρ) (hJt ((ρ ≫ c0.φ) ≫ aT.φ)) m₂ (hJu _) (hJw _) (hJ₀ _)
  have A₁ : wVal w3 z J Jw (ρ ≫ mm.φ) = gw w3 (ρ ≫ mm.φ) z (J ((ρ ≫ c0.φ) ≫ aC.φ)) (Jw (ρ ≫ mm.φ)) := by
    rw [q₁]; rfl
  have A₂ : wVal w1 z Jt Jw (ρ ≫ mm.φ) = gw w1 (ρ ≫ mm.φ) z (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) (Jw (ρ ≫ mm.φ)) := by
    rw [q₂]; rfl
  have A₃ : wVal wC z J Ju (ρ ≫ c0.φ) = gw wC (ρ ≫ c0.φ) z (J ((ρ ≫ c0.φ) ≫ aC.φ)) (Ju (ρ ≫ c0.φ)) := rfl
  have A₄ : wVal wT z Jt Ju (ρ ≫ c0.φ) = gw wT (ρ ≫ c0.φ) z (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) (Ju (ρ ≫ c0.φ)) := rfl
  rw [A₁, A₃]
  rw [A₂, A₄] at E₂
  generalize gw wC (ρ ≫ c0.φ) z (J ((ρ ≫ c0.φ) ≫ aC.φ)) (Ju (ρ ≫ c0.φ)) = A at T₁ ⊢
  generalize gw w3 (ρ ≫ mm.φ) z (J ((ρ ≫ c0.φ) ≫ aC.φ)) (Jw (ρ ≫ mm.φ)) = C' at T₁ ⊢
  generalize gw wT (ρ ≫ c0.φ) z (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) (Ju (ρ ≫ c0.φ)) = B at T₂ E₂
  generalize gw w1 (ρ ≫ mm.φ) z (Jt ((ρ ≫ c0.φ) ≫ aT.φ)) (Jw (ρ ≫ mm.φ)) = Dv at T₂ E₂
  generalize gw w0 ρ z (Ju (ρ ≫ c0.φ)) (J₀ ρ) = P at T₁ T₂
  generalize gw wm ρ z (Jw (ρ ≫ mm.φ)) (J₀ ρ) = Q at T₁ T₂
  have key : A * Dv = C' * B := by
    apply mul_right_cancel (b := P * Q)
    calc (A * Dv) * (P * Q) = (A * P) * (Dv * Q) := _root_.mul_mul_mul_comm _ _ _ _
      _ = (C' * Q) * (B * P) := by rw [T₁, T₂]
      _ = (C' * B) * (Q * P) := _root_.mul_mul_mul_comm _ _ _ _
      _ = (C' * B) * (P * Q) := by rw [_root_.mul_comm Q P]
  have key' : A ^ (N : ℤ) * Dv ^ (N : ℤ) = B ^ (N : ℤ) * C' ^ (N : ℤ) := by
    rw [← mul_zpow, key, _root_.mul_comm C' B, mul_zpow]
  apply (Units.mul_right_inj (B ^ (N : ℤ))).1
  rw [_root_.mul_left_comm, ← E₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, key']

theorem exists_frame_of_freeSec (hG : GlobalFnsSt) {R : Type} [CommRing R]
    [IsDomain R] {Z : Scheme.{0}} (t : SAB H (Sp R)) (tC : SAB H Z) (u : SAB H (Sp (FractionRing R)))
    (x : Sp (FractionRing R) ⟶ Z) (hu : IsProper u.G.hom) (aT : SABMap u t (jK R)) (aC : SABMap u tC x) (N : ℕ)
    (hF : FreeSec t N) : ∃ (n : ℕ) (f : Fin n → LB.Sec (LPow tC.G tC.PP.L (N : ℤ) (Over.mk x))),
      IsFrame tC.G tC.PP.L N x f := by
  obtain ⟨n, b, hb⟩ := hF
  obtain ⟨wT, rT⟩ := exists_rw aT
  obtain ⟨wC, rC⟩ := exists_rw aC
  obtain ⟨ΦR, a₁, a₂⟩ := exists_cmp aT.cart.1 (T := Over.mk (𝟙 (Sp (FractionRing R)))) (T₀ := Over.mk (𝟙 (Sp R))) (jK R)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨Φx, i₀, x₁, x₂⟩ := exists_iso_cmp aC.cart.1 (𝟙 (Sp (FractionRing R))) x (Category.id_comp _)
  choose a hA using fun i => exists_thr_down ((isGen_iff _).2 rT.1) t.PP.isLB u.PP.isLB a₂ (b i)
  choose f hf using fun i => exists_thr_iso ((isGen_iff _).2 rC.1) tC.PP.isLB u.PP.isLB x₂ (a i)
  refine ⟨n, f, fun W _ _ _ hW φ gam hg χ h => ?_⟩
  have hinj : Function.Injective φ := fun p q e => IsFractionRing.injective R (FractionRing R)
    (gam.injective (by rw [hg, hg, e]))
  obtain ⟨Dd, tW, c0, mm, a1, a3, hD, e₁, e₂⟩ := exists_trait_map hu aT aC hW φ gam hg χ h
  obtain ⟨w0, r0⟩ := exists_rw c0
  obtain ⟨wm, rm⟩ := exists_rw mm
  obtain ⟨w1, r1⟩ := exists_rw a1
  obtain ⟨w3, r3⟩ := exists_rw a3
  have g1 := (isGen_iff _).2 r1.1
  have g3 := (isGen_iff _).2 r3.1
  obtain ⟨Φ1, p₁, p₂⟩ := exists_cmp a1.cart.1 (T := Over.mk (𝟙 (Sp W))) (T₀ := Over.mk (𝟙 (Sp R))) (spMap φ)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨Φ1', i₁, q₁, q₂⟩ := exists_iso_cmp a1.cart.1 (𝟙 (Sp W)) (spMap φ) (Category.id_comp _)
  obtain ⟨Φ3, i₃, s₁, s₂⟩ := exists_iso_cmp a3.cart.1 (𝟙 (Sp W)) χ (Category.id_comp _)
  choose c hc using fun i => exists_thr_down g1 t.PP.isLB tW.PP.isLB p₂ (b i)
  choose b' hb' using fun i => exists_thr_iso g3 tC.PP.isLB tW.PP.isLB s₂ (c i)
  have B₁ : BasisAlong tW.G tW.PP.L N (𝟙 _) c :=
    (basis_thr_iff g1 t.PP.isLB tW.PP.isLB (h₀ := toBase φ) (h := 𝟙 _) q₁ q₂
      (cmp_comm p₁ p₂ q₁ q₂ ((Category.id_comp _).trans (Category.id_comp _).symm)) hc).1 (hb W hW φ hinj)
  have B₂ : BasisAlong tC.G tC.PP.L N (𝟙 _) b' :=
    (basis_thr_iff g3 tC.PP.isLB tW.PP.isLB (h₀ := 𝟙 _) (h := 𝟙 _) s₁ s₂
      (by rw [id_whiskerRight, id_whiskerRight, Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]) hb').2 B₁
  refine ⟨b', B₂, fun i => ?_⟩
  obtain ⟨s, hs⟩ := exists_isPull (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (b' i)
  refine ⟨s, lin_one_of fun Y r z J hJ => (hs Y r z J hJ).trans ?_, lin_one_of hs⟩
  exact (value_eq hG h (ArcExtends.spMap_jK hg) hD e₁ e₂ rT rC r0 rm r1 r3 a₁ a₂ x₁ x₂ p₁ p₂ s₁ s₂ (hA i) (hf i) (hc i)
    (hb' i) r z hJ).symm

end Frames

theorem extendSt : ExtendSt := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' C Y R _ _ _ ξ t mt y b m hR hy hs ⟨Z, π, tZ, mZ, hfin, hsurj, ⟨Am⟩⟩ h1 hm
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨_, _, hc, _⟩ := hR
  have := hfin
  have := hsurj
  obtain ⟨u, ⟨n₀⟩⟩ := exists_sabPull y C.oF.t
  obtain ⟨aC, -⟩ := LevelCover.sab_comp n₀ C.m (e := y ≫ C.j) rfl
  obtain ⟨n₁, -⟩ := LevelCover.sab_comp n₀ C.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := LevelCover.sab_cancel Y.m0.toSABMap n₁ y rfl
  obtain ⟨n₃, -⟩ := LevelCover.sab_comp n₂ Y.m (e := y ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := LevelCover.sab_cancel mt n₃ (jK R) hy.symm
  have hu : IsProper u.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 C.oF.proper
  obtain ⟨k₁, f₁, hf₁⟩ := exists_frame_of_freeSec hL.globalFns t C.t u (y ≫ C.j) hu aT aC 1 h1
  obtain ⟨n, f₂, hf₂⟩ := exists_frame_of_freeSec hL.globalFns t C.t u (y ≫ C.j) hu aT aC (m ^ 2) hm
  let g : R →+* R := RingHom.id R
  let gam : FractionRing R →+* FractionRing R := RingHom.id _
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap R _ (g r) := fun _ => rfl
  obtain ⟨L, _, σ, z, hσ, hz⟩ := ArcExtends.exists_lift_finite π (y ≫ C.j)
  obtain ⟨R₂, _, _, _, _, _, hch, g₂, f, hf, hint⟩ :=
    ArcExtends.exists_normalisation R hc hgam (RingHom.Finite.id R) hσ
  have hx : (spMap f ≫ z) ≫ π = spMap (f.comp σ) ≫ y ≫ C.j := by
    rw [Category.assoc, hz, spMap_comp, Category.assoc]
  have hP := ArcExtends.polAt_moduli C y
  obtain ⟨θ, hθ, bθ⟩ := FramePull.frame_pull hL hL₂ E H _ Z C.t tZ π mZ R R₂ g₂ _ hf _ _ hx hP 1 k₁ _ hf₁
  obtain ⟨ff, hff, bff⟩ := FramePull.frame_pull hL hL₂ E H _ Z C.t tZ π mZ R R₂ g₂ _ hf _ _ hx hP (m ^ 2) n _ hf₂
  have hab : Set.range (spMap f ≫ z) ⊆ abLocus tZ.G := by
    rintro _ ⟨p, rfl⟩
    refine (abLocus_pullback abLocusOne C.t.semi mZ.cart.1 _).1 (abLocusOne _ C.t.G C.t.semi _ _ hP.1 ?_)
    exact ⟨spMap (f.comp σ) p, (congrArg (fun q => q p) hx).symm⟩
  have tθ : ∀ i, FrameGen.TraitBasis tZ.G tZ.PP.L 1 (Am.A.U i) (fun _ : Fin 1 => Am.th i) :=
    fun i W _ _ _ hW χ h => (Am.trait i W hW χ h).1
  obtain ⟨i₀, hi₀⟩ := FrameGen.exists_chart_local Am.isLB (spMap f ≫ z)
  obtain ⟨xi⟩ := FrameGen.exists_lift (spMap f ≫ z) _ hi₀
  obtain rfl : k₁ = 1 := FrameGen.card_eq tZ.PP.isLB (tθ i₀) hab hθ bθ xi
  obtain ⟨θ', rfl⟩ : ∃ θ', θ = fun _ : Fin 1 => θ' := ⟨θ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨e, he, hE⟩ := FrameGen.exists_gen_of_frames Z tZ.G tZ.PP.L tZ.PP.isLB (m ^ 2) Am Am.A rfl R₂ _ hab θ' n ff hθ hff bθ bff hch
  have := projProper _ _ _ C.proj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ C.s)
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ C.s)
  have hG : ∀ r, ((f.comp σ).comp gam) (algebraMap R _ r) = algebraMap R₂ _ ((g₂.comp g) r) := fun r =>
    (congrArg (f.comp σ) (hgam r)).trans (hf _)
  have hx' : (spMap f ≫ z) ≫ π = spMap ((f.comp σ).comp gam) ≫ y ≫ C.j := hx
  obtain ⟨χ₂, hχ₂⟩ := ExtLB.exists_extension Z Am.A Am.isLB Am.ample R₂ _ e he fun V _ _ _ hV φ gV hgV => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists (π ≫ C.s) (spMap gV ≫ spMap f ≫ z)
      (spMap φ ≫ spMap (g₂.comp g) ≫ spMap b) (by
        rw [Category.assoc, ← Category.assoc (spMap f ≫ z), hx', Category.assoc, Category.assoc, hs,
          ← Category.assoc (spMap _) (jK _), ArcExtends.spMap_jK hG, Category.assoc, ← Category.assoc (spMap gV),
          ArcExtends.spMap_jK hgV, Category.assoc])
    exact ⟨χ, hχ.symm, hE V hV φ gV hgV χ hχ.symm⟩
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.extension_descends_of_isIntegral _ R₂ _ _ hG hint C.X (y ≫ C.j) (χ₂ ≫ π)
    (by rw [← Category.assoc, hχ₂, hx'])
  exact ⟨χ, hχ⟩

end GlobalTheory.TorRef
