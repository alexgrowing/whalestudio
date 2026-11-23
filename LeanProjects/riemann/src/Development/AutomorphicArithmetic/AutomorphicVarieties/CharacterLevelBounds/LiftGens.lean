import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenLeAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem lift_gens {Γ Q : Type} [Group Γ] [Group Q] (p : Γ →* Q) (hp : Function.Surjective p)
    (T : Finset Q) (hT : Subgroup.closure (T : Set Q) = ⊤) :
    ∃ T' : Finset Γ, T'.card ≤ T.card ∧ ⊤ ≤ Subgroup.closure (T' : Set Γ) ⊔ p.ker := by
  classical
  choose s hs using hp
  refine ⟨T.image s, Finset.card_image_le, ?_⟩
  rw [← Subgroup.comap_map_eq, MonoidHom.map_closure, Finset.coe_image, Set.image_image]
  simp only [hs, Set.image_id', hT, Subgroup.comap_top, le_refl]

theorem UpperTheory.V.Chr.upV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω] [IsAbelianGalois k L]
          (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (D : LData L Ω l) (e : ℕ) (ψ : G k Ω →* Oˣ), galOf k L Ω ≤ ψ.ker →
          ∀ T : Finset (L ≃ₐ[k] L), Subgroup.closure (T : Set (L ≃ₐ[k] L)) = ⊤ →
          V l e ψ ≤ shaLen D (e : ℤ) * eO l O + (T.card : ℕ∞) * h0 l e ψ ⊤ := by
  intro k Ω _ _ _ _ _ L _ _ _ _ _ _ _ l _ O _ _ _ _ _ D e ψ hψ T hT
  obtain ⟨hp, hker, -⟩ := galQuot k L Ω
  obtain ⟨T', hc, hT'⟩ := lift_gens _ hp T hT
  have hab : ∀ a ∈ (⊤ : Subgroup (G k Ω)), ∀ b ∈ (⊤ : Subgroup (G k Ω)), a * b * a⁻¹ * b⁻¹ ∈ galOf k L Ω := by
    intro a _ b _
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm' (AlgEquiv.restrictNormalHom L a)]
    simp
  rw [hker] at hT'
  have hopen : IsOpen ((ψ⁻¹ : G k Ω →* Oˣ).ker : Set (G k Ω)) :=
    Subgroup.isOpen_mono (H₁ := galOf k L Ω) (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.mem_ker.1 (hψ hg), inv_one]) (galEmbTop k L Ω).2.1
  have hk := kerResAb O (G k Ω) (QO l O) (rho l e ψ) ((contTw k Ω l).2.2 O _ _ hopen) (qoFacts l O).1
    (fun g => ⟨_, fun m => scalRep_apply _ _ g m⟩) (galOf k L Ω) ⊤ le_top hab T' (fun _ _ => trivial)
    (hT'.trans (Subgroup.le_topologicalClosure _))
  obtain ⟨⟨Φ, -⟩, -⟩ := selTwist O (G k Ω) (QO l O) _ (rho l e ψ) ψ (tw_apply l e ψ) (galOf k L Ω)
    (fun u hu => hψ hu) _ (conjStable_shaFam k Ω l)
  have hχ : chiO k Ω l O ^ (-(e : ℤ)) =
      (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-(e : ℤ))) :=
    MonoidHom.ext fun g => (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) _).symm
  have hb := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-(e : ℤ))) (galOf k L Ω) (shaFam k Ω l)).1
  rw [← hχ, Φ.length_eq] at hb
  have hs : shaLen D (e : ℤ) = _ := (shaLenEq k L Ω l D e).1
  refine (selUp O (G k Ω) (QO l O) (rho l e ψ) (galOf k L Ω) ⊤ le_top _ (conjStable_shaFam k Ω l)).1.trans
    (add_le_add (le_of_eq ?_) (hk.trans ?_))
  · rw [hs]
    exact hb
  · unfold h0
    gcongr
